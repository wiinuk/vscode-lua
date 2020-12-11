[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module LuaChecker.Server.ProjectAgent
open LuaChecker
open LuaChecker.Server.Log
open LuaChecker.Server.Protocol
open LuaChecker.Text.Json
open System
open System.Text
open System.Text.Json
open type LuaChecker.Server.Marshalling.MarshallingContext
open type LuaChecker.Server.ProjectAgent
type private M = Protocol.Methods


[<AutoOpen>]
module private Helpers =
    let sendRequest agent methods parameters handler =
        let id = agent.nextRequestId
        let jsonBytes =
            JsonRpcMessage.request id methods parameters
            |> Json.serialize
            |> ReadOnlyMemory

        agent.writer.Post <| WriteMessage jsonBytes

        let handler struct(agent, result) =
            let result = Result.map JsonElement.parse result
            handler struct(agent, result)

        { agent with
            nextRequestId = agent.nextRequestId + 1
            responseHandlers = Map.add id handler agent.responseHandlers
        }

    let sendResponse id (agent, result) =
        let jsonBytes =
            match result with
            | Ok result -> JsonRpcMessage.successResponse id result
            | Error e -> JsonRpcMessage.errorResponse id e
            |> Json.serialize
            |> ReadOnlyMemory

        agent.writer.Post <| WriteMessage jsonBytes
        agent

    let sendNotification agent methods parameters =
        let jsonBytes =
            JsonRpcMessage.notification methods parameters
            |> Json.serialize
            |> ReadOnlyMemory

        agent.writer.Post <| WriteMessage jsonBytes

    let publishDiagnostics agent filePath diagnostics =
        {
            uri = DocumentPath.toUri(filePath).ToString()
            diagnostics = diagnostics
        }
        |> ValueSome
        |> sendNotification agent
            M.``textDocument/publishDiagnostics``

    let checkAndResponseSingleFile agent path =
        match Map.tryFind path agent.documents with
        | ValueNone -> ifError { trace "unopened file: %A" path }; agent, []
        | ValueSome document ->

        ifDebug { trace "begin check %A" path }
        ifDebug { agent.watch.Restart() }
        let _, diagnostics, project, descendants = Checker.parseAndCheckCached agent.project path (InMemory(document.contents, document.version))
        ifDebug { trace "check %dms %A" agent.watch.ElapsedMilliseconds path }

        let agent = { agent with project = project }

        let context = {
            documents = agent.documents
            resources = agent.resources
            root = agent.root
        }
        let diagnostics = Marshalling.marshalDocumentDiagnostics context path document diagnostics
        publishDiagnostics agent path <| Seq.toArray diagnostics

        agent, descendants

    let addBackgroundCheckFiles files agent =
        match files with
        | [] -> agent
        | _ ->

        let mutable temp = agent.pendingBackgroundCheckPaths
        for path in files do
            temp <- Set.add path agent.pendingBackgroundCheckPaths
        { agent with pendingBackgroundCheckPaths = temp }

    let checkAndResponse agent path =
        let agent, descendants = checkAndResponseSingleFile agent path
        addBackgroundCheckFiles descendants agent

    let popMinElement set =
        if Set.isEmpty set then None else
        let e = Set.minElement set
        Some(e, Set.remove e set)

    let (?) (json: JsonElement) (name: string) = json.GetProperty name

let initialize agent { rootUri = rootUri } =
    let agent =
        match rootUri with
        | ValueSome root -> { agent with ProjectAgent.root = root }
        | _ -> agent

    agent, Ok {
        capabilities = {
            hoverProvider = true
            textDocumentSync = {
                openClose = true
                save = Defined { includeText = false }
                change = TextDocumentSyncKind.Incremental
            }
        }
    }

let initialized agent =
    let options = {|
        watchers = [|
            {| globPattern = "**/*.lua" |}
        |]
    |}
    let ps = {|
        registrations = [|
            {|
                id = Guid.NewGuid()
                method = M.``workspace/didChangeWatchedFiles``
                registerOptions = options
            |}
        |]
    |}
    let responseHandler struct(agent, r) =
        match r with
        | Error e -> ifWarn { Log.Format(agent.resources.LogMessages.ErrorResponseReceived, e) }
        | Ok() -> ()
        agent

    sendRequest agent M.``client/registerCapability`` (ValueSome ps) responseHandler

let shutdown agent () =
    agent, Ok()

let didOpenTextDocument agent { DidOpenTextDocumentParams.textDocument = d } =
    let path = DocumentPath.ofUri agent.root d.uri
    let agent = { agent with documents = Documents.open' path d.text d.version agent.documents }

    checkAndResponse agent path

let didChangeTextDocument agent { textDocument = d; contentChanges = contentChanges } =
    let path = DocumentPath.ofUri agent.root d.uri
    let documents = Documents.change path d.version contentChanges agent.documents
    { agent with documents = documents }
    |> addBackgroundCheckFiles [path]

let didCloseTextDocument agent (p: DidCloseTextDocumentParams) =
    let path = DocumentPath.ofUri agent.root p.textDocument.uri
    let agent = { agent with documents = Documents.close path agent.documents }
    publishDiagnostics agent path [||]
    agent

let didSaveTextDocument agent { DidSaveTextDocumentParams.textDocument = textDocument } =
    let savedFile = DocumentPath.ofUri agent.root textDocument.uri
    let files = [
        for path in Documents.openedPaths agent.documents do
            if Checker.isAncestor savedFile path agent.project then
                path
    ]
    addBackgroundCheckFiles files agent

let didChangeWatchedFiles agent { changes = changes } =
    let mutable agent = agent
    for change in changes do
        let path = DocumentPath.ofUri agent.root change.uri
        ifDebug { trace "changed %A %A" path change.``type`` }

        let (DocumentPath p) = path
        if p.EndsWith ".lua" then
            let struct(project, descendants) =
                match change.``type`` with
                | FileChangeType.Created -> Checker.addOrUpdateSourceFile path agent.project
                | FileChangeType.Changed -> Checker.addOrUpdateSourceFile path agent.project
                | FileChangeType.Deleted -> Checker.removeSourceFile path agent.project
                | t ->
                    ifWarn { trace "unknown FileChangeType: %A" t }
                    agent.project, []

            agent <- { agent with project = project }
            agent <- addBackgroundCheckFiles (path::descendants) agent
    agent

let hover agent { HoverParams.textDocument = textDocument; position = position } =
    let path = DocumentPath.ofUri agent.root textDocument.uri
    match Documents.tryFind path agent.documents with
    | ValueNone -> agent, Ok ValueNone
    | ValueSome document ->

    let index = Document.positionToIndex position document
    let context = {
        root = agent.root
        resources = agent.resources
        documents = agent.documents
    }
    let result, project = Checker.hitTest agent.project Marshalling.prettyTokenInfo context path index
    let agent = { agent with project = project }

    match result with
    | ValueNone -> agent, Ok ValueNone
    | ValueSome markdown ->

    let markdown = { kind = MarkupKind.markdown; value = markdown }
    agent, Ok (ValueSome { contents = markdown; range = Undefined })

let processPendingRequest agent path =
    fst <| checkAndResponseSingleFile agent path

let processNotification agent methods ps =
    match methods with
    | M.initialized -> initialized agent
    | M.``textDocument/didOpen`` ->
        didOpenTextDocument agent (JsonElement.parse ps)

    | M.``textDocument/didChange`` ->
        didChangeTextDocument agent (JsonElement.parse ps)

    | M.``textDocument/didClose`` ->
        didCloseTextDocument agent (JsonElement.parse ps)

    //| M.``workspace/didChangeConfiguration`` -> didChangeConfiguration agent ps
    | M.``textDocument/didSave`` -> didSaveTextDocument agent <| JsonElement.parse ps
    | M.``workspace/didChangeWatchedFiles`` -> didChangeWatchedFiles agent <| JsonElement.parse ps

    | method ->
        ifWarn { Log.Format(agent.resources.LogMessages.UnknownNotification, method, ps) }
        agent

let processRequest agent id ps = function
    | M.initialize -> JsonElement.parse ps |> initialize agent |> sendResponse id
    | M.``textDocument/hover`` -> JsonElement.parse ps |> hover agent |> sendResponse id 
    //| M.``workspace/didChangeWorkspaceFolders`` ->
    | M.shutdown -> JsonElement.parse ps |> shutdown agent |> sendResponse id

    | method ->
        ifError { Log.Format(agent.resources.LogMessages.UnknownRequest, id, method, ps) }
        let error = {
            code = JsonRpcErrorCodes.MethodNotFound
            message = "method not found"
            data = Undefined
        }
        sendResponse id (agent, Error(ValueSome error))

let processResponse agent id result =
    match Map.tryFind id agent.responseHandlers with
    | ValueSome handler -> handler(agent, result)
    | _ ->
        ifWarn { Log.Format(agent.resources.LogMessages.ResponseHandlerNotFound, id, result) }
        agent

let processMessage agent = function
    | { method = Defined M.``$/cancelRequest``; ``params`` = Defined _ } ->
        // TODO:
        agent

        //let id = ps?id.GetInt32()

        //let mutable cancel = null
        //if server.pipe.pendingRequests.TryGetValue(id, &cancel) then
        //    cancel.Cancel()
        //    ifInfo { Log.Format(server.resources.LogMessages.RequestCanceled, id) }

    | { id = Undefined; method = Defined method; ``params`` = ps } ->
        let ps = OptionalField.defaultValue (JsonElement()) ps
        processNotification agent method ps

    | { id = Defined id; method = Defined method; ``params`` = json } ->
        let json = OptionalField.defaultValue (JsonElement()) json
        processRequest agent id json method

    | { id = Defined id; result = Defined result } ->
        processResponse agent id (Ok result)

    | { id = Defined id; result = Undefined; error = error } ->
        processResponse agent id <| Error(OptionalField.toVOption error)

    | message ->
        ifInfo { Log.Format(agent.resources.LogMessages.InvalidMessageFormat, message) }
        agent

let create state = new MailboxProcessor<_>(fun inbox ->
    let rec loop agent = async {
        match! inbox.TryReceive(timeout = 0) with

        // 新しいリクエストを処理
        | Some message -> return! dispatchMessage agent message

        // 新しいリクエストが無かった
        | None ->

        match popMinElement agent.pendingBackgroundCheckPaths with

        // 保留中の処理も無いので新しいメッセージが来るまで待機
        | None ->
            let! message = inbox.Receive()
            return! dispatchMessage agent message

        // 保留中の処理を実行
        | Some(r, set) ->
            let agent = { agent with pendingBackgroundCheckPaths = set }
            let agent = processPendingRequest agent r
            return! loop agent
        }
    and dispatchMessage agent message = async {
        match message with
        | QuitProjectAgent -> return ()
        | ProcessReceivedMessage message ->
            let agent = processMessage agent message
            return! loop agent
    }
    loop state
)
