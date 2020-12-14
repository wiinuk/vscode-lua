[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module LuaChecker.Server.ProjectAgent
open LuaChecker
open LuaChecker.Server.Log
open LuaChecker.Server.Protocol
open LuaChecker.Text.Json
open System
open System.IO
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

        agent.writeAgent.Post <| WriteMessage jsonBytes

        let handler struct(agent, result) =
            let result = Result.map JsonElement.parse result
            handler struct(agent, result)

        { agent with
            nextRequestId = agent.nextRequestId + 1
            responseHandlers = Map.add id handler agent.responseHandlers
        }

    let sendResponse agent id result =
        WriteAgent.sendResponse agent.writeAgent id result

    let postToBackgroundAgent { random = random; backgroundAgents = backgroundAgents } message =
        backgroundAgents.[random.Next(0, backgroundAgents.Length)].Post message

    let checkAndResponseSingleFile agent path =
        let document = Map.tryFind path agent.documents
        let source =
            match document with
            | ValueNone -> InFs(path, agent.project.projectRare.fileSystem.lastWriteTime path)
            | ValueSome document -> InMemory(document.contents, document.version)

        ifDebug { Log.Format(agent.resources.LogMessages.BeginCheck, DocumentPath.toLocalPath path) }
        ifDebug { agent.watch.Restart() }
        let _, diagnostics, project, descendants = Checker.parseAndCheckCached agent.project path source
        ifDebug { Log.Format(agent.resources.LogMessages.EndCheck, agent.watch.ElapsedMilliseconds, DocumentPath.toLocalPath path) }

        let agent = { agent with project = project }

        match document with
        | ValueNone -> ifDebug { Log.Format(agent.resources.LogMessages.UnopenedFileDiagnosticsIsNotPublished, path) }
        | ValueSome document ->
            postToBackgroundAgent agent <| PublishDiagnostics(agent, path, ValueSome document, diagnostics)

        agent, descendants

    let addLowPriorityCheckFiles files agent =
        match files with
        | [] -> agent
        | _ ->

        let mutable temp = agent.pendingCheckPaths
        for path in files do
            temp <- Set.add path agent.pendingCheckPaths
        { agent with pendingCheckPaths = temp }

    let checkAndResponse agent path =
        let agent, descendants = checkAndResponseSingleFile agent path
        addLowPriorityCheckFiles descendants agent

    let popMinElement set =
        if Set.isEmpty set then None else
        let e = Set.minElement set
        Some(e, Set.remove e set)

    let processFileEvent agent path change =
        let mutable agent = agent
        let struct(project, descendants) =
            match change.``type`` with
            | FileChangeType.Created
            | FileChangeType.Changed -> Checker.addOrUpdateSourceFile path agent.project
            | FileChangeType.Deleted -> Checker.removeSourceFile path agent.project
            | t ->
                ifWarn { trace "unknown FileChangeType: %A" t }
                agent.project, []

        agent <- { agent with project = project }
        agent <- addLowPriorityCheckFiles (path::descendants) agent
        agent

    let checkProjectFileOrCachedResult agent path project =
        match Project.tryFind path project with
        | ValueSome sourceFile ->
            ifDebug { Log.Format(agent.resources.LogMessages.BeginCheck, DocumentPath.toLocalPath path) }
            ifDebug { agent.watch.Restart() }
            let typedTree, diagnostics, project = Checkers.checkSourceFileCached project path sourceFile
            ifDebug { Log.Format(agent.resources.LogMessages.EndCheck, agent.watch.ElapsedMilliseconds, DocumentPath.toLocalPath path) }
            Some typedTree, diagnostics, project

        | ValueNone -> None, upcast [], project

let initialize agent id { rootUri = rootUri } =
    let agent =
        match rootUri with
        | ValueSome root -> { agent with ProjectAgent.root = root }
        | _ -> agent

    sendResponse agent id <| Ok {
        capabilities = {
            hoverProvider = true
            textDocumentSync = {
                openClose = true
                save = Defined { includeText = false }
                change = TextDocumentSyncKind.Incremental
            }
        }
    }
    agent

let initialized inbox agent =
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
    let responseHandler inbox struct(agent, r) =
        match r with
        | Error e ->
            ifWarn { Log.Format(agent.resources.LogMessages.ErrorResponseReceived, e) }
            agent

        | Ok() ->
            postToBackgroundAgent agent <| EnumerateFiles(agent.project.projectRare.fileSystem, agent.root, inbox)
            agent

    sendRequest agent M.``client/registerCapability`` (ValueSome ps) (responseHandler inbox)

let shutdown agent id () =
    sendResponse agent id <| Ok()
    agent

let didOpenTextDocument agent { DidOpenTextDocumentParams.textDocument = d } =
    let path = DocumentPath.ofUri agent.root d.uri
    let agent = { agent with documents = Documents.open' path d.text d.version agent.documents }
    checkAndResponse agent path

let didChangeTextDocument agent { textDocument = d; contentChanges = contentChanges } =
    let path = DocumentPath.ofUri agent.root d.uri
    let documents = Documents.change path d.version contentChanges agent.documents
    { agent with documents = documents }
    |> addLowPriorityCheckFiles [path]

let didCloseTextDocument agent (p: DidCloseTextDocumentParams) =
    let path = DocumentPath.ofUri agent.root p.textDocument.uri
    let agent = { agent with documents = Documents.close path agent.documents }
    postToBackgroundAgent agent <| PublishDiagnostics(agent, path, ValueNone, [])
    agent

let didSaveTextDocument agent { DidSaveTextDocumentParams.textDocument = textDocument } =
    let savedFile = DocumentPath.ofUri agent.root textDocument.uri
    let files = [
        for path in Documents.openedPaths agent.documents do
            if Checker.isAncestor savedFile path agent.project then
                path
    ]
    addLowPriorityCheckFiles files agent

let didChangeWatchedFiles agent { changes = changes } =
    let mutable agent' = agent
    for change in changes do
        let path = DocumentPath.ofUri agent'.root change.uri
        ifDebug { Log.Format(agent.resources.LogMessages.FileChanged, DocumentPath.toLocalPath path, change.``type``) }

        let (DocumentPath p) = path
        if p.EndsWith ".lua" then
            agent' <- processFileEvent agent' path change
    agent'

let hover agent id { HoverParams.textDocument = textDocument; position = position } =
    let path = DocumentPath.ofUri agent.root textDocument.uri
    match Documents.tryFind path agent.documents with
    | ValueNone -> sendResponse agent id <| Ok ValueNone; agent
    | ValueSome document ->

    let tree, _, project = checkProjectFileOrCachedResult agent path agent.project
    let agent = { agent with project = project }

    match tree with
    | None -> sendResponse agent id <| Ok ValueNone; agent
    | Some tree ->
        postToBackgroundAgent agent <| HoverHitTestAndResponse(id, agent, document, tree, position)
        agent

let processPendingRequest agent path =
    fst <| checkAndResponseSingleFile agent path

let processNotification inbox agent methods ps =
    match methods with
    | M.initialized -> initialized inbox agent
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
    | M.initialize -> JsonElement.parse ps |> initialize agent id
    | M.``textDocument/hover`` -> JsonElement.parse ps |> hover agent id
    //| M.``workspace/didChangeWorkspaceFolders`` ->
    | M.shutdown -> JsonElement.parse ps |> shutdown agent id

    | method ->
        ifError { Log.Format(agent.resources.LogMessages.UnknownRequest, id, method, ps) }
        let error = {
            code = JsonRpcErrorCodes.MethodNotFound
            message = "method not found"
            data = Undefined
        }
        sendResponse agent id <| Error(ValueSome error)
        agent

let processResponse agent id result =
    match Map.tryFind id agent.responseHandlers with
    | ValueSome handler -> handler(agent, result)
    | _ ->
        ifWarn { Log.Format(agent.resources.LogMessages.ResponseHandlerNotFound, id, result) }
        agent

let processMessage inbox agent = function
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
        processNotification inbox agent method ps

    | { id = Defined id; method = Defined method; ``params`` = json } ->
        let json = OptionalField.defaultValue (JsonElement()) json
        processRequest agent id json method

    | { id = Defined id; result = Defined result } ->
        processResponse agent id <| Ok result

    | { id = Defined id; result = Undefined; error = error } ->
        processResponse agent id <| Error(OptionalField.toVOption error)

    | message ->
        ifWarn { Log.Format(agent.resources.LogMessages.InvalidMessageFormat, message) }
        agent

let processEnumerateFilesResponse agent files =
    let mutable agent = agent
    for filePath in files do
        match DocumentPath.toLocalPath filePath |> Path.GetExtension with
        | ".lua" ->
            agent <- processFileEvent agent filePath {
                uri = DocumentPath.toUri filePath
                ``type`` = FileChangeType.Created
            }
        | _ -> ()
    agent

let create state = new MailboxProcessor<_>(fun inbox ->
    let rec loop agent = async {
        match! inbox.TryReceive(timeout = 0) with

        // 新しいリクエストを処理
        | Some message -> return! dispatchMessage agent message

        // 新しいリクエストが無かった
        | None ->

        match popMinElement agent.pendingCheckPaths with

        // 保留中の処理も無いので新しいメッセージが来るまで待機
        | None ->
            let! message = inbox.Receive()
            return! dispatchMessage agent message

        // 保留中の処理を実行
        | Some(r, set) ->
            let agent = { agent with pendingCheckPaths = set }
            let agent = processPendingRequest agent r
            return! loop agent
        }
    and dispatchMessage agent message = async {
        match message with
        | QuitProjectAgent ->
            agent.writeAgent.Post QuitWriteAgent
            do for agent in agent.backgroundAgents do agent.Post QuitBackgroundAgent
            return ()

        | ProcessReceivedMessage message ->
            return! loop <| processMessage inbox agent message

        | EnumerateFilesResponse files ->
            return! loop <| processEnumerateFilesResponse agent files
    }
    loop state
)
