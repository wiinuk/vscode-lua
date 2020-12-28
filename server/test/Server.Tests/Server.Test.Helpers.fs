module LuaChecker.Server.Test.Helpers
open FSharp.Data.UnitSystems.SI.UnitSymbols
open LuaChecker
open LuaChecker.Checker.Test.Helpers
open LuaChecker.Server
open LuaChecker.Server.Json
open LuaChecker.Server.Log
open LuaChecker.Server.Protocol
open LuaChecker.Text.Json
open System
open System.Collections.Concurrent
open System.Diagnostics
open System.IO
open System.Text.Json
open System.Threading
open Xunit.Abstractions
module MessageWriter = LuaChecker.Server.Protocol.Tests.MessageWriter


type Async with
    static member ParallelAction(xs: unit Async seq) =
        Async.Parallel xs |> Async.Ignore

[<Sealed>]
type BlockingStream() =
    inherit Stream()
    let blocks = new BlockingCollection<_>()
    let mutable remainingBlock = ReadOnlyMemory.Empty

    override _.CanTimeout = true
    override val ReadTimeout = Timeout.Infinite with get, set
    override val WriteTimeout = Timeout.Infinite with get, set

    override _.Length = raise <| NotSupportedException()
    override _.SetLength _ = raise <| NotSupportedException()

    override _.CanSeek = false
    override _.Seek(_, _) = raise <| NotSupportedException()
    override _.Position
        with get() = raise <| NotSupportedException()
        and set _ = raise <| NotSupportedException()

    override _.CanWrite = true
    override s.Write(buffer, offset, count) =
        let block = Memory(Array.zeroCreate count)
        ReadOnlyMemory(buffer, offset, count).CopyTo block
        if not <| blocks.TryAdd(Memory.op_Implicit block, s.WriteTimeout) then
            raise <| TimeoutException()

    override _.CanRead = true
    override s.Read(buffer, offset, count) =
        let output = Span(buffer, offset, count)

        let mutable block = remainingBlock
        let mutable remainingOutput = output
        while
            if remainingOutput.IsEmpty then
                false

            elif block.IsEmpty then
                blocks.TryTake(&block, s.ReadTimeout)

            else
                let copyLength = min remainingOutput.Length block.Length
                block.Slice(0, copyLength).Span.CopyTo remainingOutput
                remainingOutput <- remainingOutput.Slice copyLength
                block <- block.Slice copyLength
                true
            do ()

        remainingBlock <- block
        output.Length - remainingOutput.Length

    override _.Flush() = ()

    override _.Dispose disposing =
        base.Dispose disposing
        if disposing then
            blocks.Dispose()

    override _.Close() =
        blocks.CompleteAdding()
        base.Close()

    member _.CompleteWriting() =
        blocks.CompleteAdding()

type ProtocolMessage =

    // request & response
    | Initialize of InitializeParams
    | InitializeResponse of InitializeResult
    | RegisterCapability of RegistrationParams
    | RegisterCapabilityResponse
    | Hover of HoverParams
    | HoverResponse of Hover voption
    | Shutdown
    | ShutdownResponse
    | SemanticTokensFull of SemanticTokensParams
    | SemanticTokensFullResponse of SemanticTokens voption
    | SemanticTokensRange of SemanticTokensRangeParams
    | SemanticTokensRangeResponse of SemanticTokens voption

    // notification
    | Initialized
    | DidOpen of DidOpenTextDocumentParams
    | DidChange of DidChangeTextDocumentParams
    | PublishDiagnostics of PublishDiagnosticsParams
    | DidSave of DidSaveTextDocumentParams
    | DidChangeWatchedFiles of DidChangeWatchedFilesParams
    | Exit

type Actions =
    | Send of ProtocolMessage
    | Sleep of float<s>
    | WriteFile of path: DocumentPath * contents: string
    | ReceiveRequest of tryResponse: (ProtocolMessage -> Result<ProtocolMessage, JsonRpcResponseError voption> option) * timeout: float<s> option
    | WaitUntil of predicate: (ProtocolMessage list -> bool) * timeout: float<s> option

/// `Send(DidOpen { … })`
let (&>) source (path, version) = Send <| DidOpen {
    textDocument = {
        text = source
        uri = Uri path
        version = version
    }
}

type Message =
    | Request of id: int * ``params``: ProtocolMessage
    | Response of id: int * result: JsonElement
    | Notification of ``params``: ProtocolMessage

let parseMessage x =
    match x with

    // request
    | { method = Defined m; id = Defined id } ->
        let request =
            match m, x.``params`` with
            | Methods.``client/registerCapability``, Defined ps ->
                RegisterCapability <| JsonElement.parse<RegistrationParams> ps

            | _ -> failwith $"TODO: request: %A{x}"

        Request(id, request)

    // notification
    | { method = Defined m; id = Undefined; ``params`` = ps } ->
        let x =
            match m, ps with
            | Methods.``textDocument/publishDiagnostics``, Defined ps ->
                PublishDiagnostics <| JsonElement.parse<PublishDiagnosticsParams> ps

            | _ -> failwithf "TODO: notification: %A" x

        Notification x

    | { id = Undefined } -> failwithf "required id: %A" x
    | { result = Undefined } -> failwithf "response with error: %A" x

    // response
    | { id = Defined id; result = Defined result } ->
        Response(id, result)

type ConnectionConfig = {
    readTimeout: TimeSpan
    writeTimeout: TimeSpan
    /// e.g. : `fun t -> if Debugger.IsAttached then ...`
    timeoutMap: TimeSpan -> TimeSpan
    backgroundCheckDelay: TimeSpan
    serverPlatform: PlatformID option
    initialFiles: {| source: string; uri: string |} list
    rootUri: Uri
    createFileSystem: unit -> FileSystem
    globalModuleFiles: {| source: string; path: string |} list
}
module ConnectionConfig =
    let defaultValue = {
        readTimeout = TimeSpan.FromSeconds 5.
        writeTimeout = TimeSpan.FromSeconds 5.
        timeoutMap = fun x -> if Debugger.IsAttached then Timeout.InfiniteTimeSpan else x
        backgroundCheckDelay = TimeSpan.Zero
        serverPlatform = Some PlatformID.Win32NT
        initialFiles = []
        globalModuleFiles = [
            for path in Server.ServerCreateOptions.defaultOptions.globalModulePaths do
                let path = Path.GetFullPath path
                {| path = path; source = File.ReadAllText path |}
        ]
        rootUri = Uri "file:///C:/"
        createFileSystem = FileSystem.memory
    }
type Client<'V,'R> = {
    clientToServer: Stream
    serverToClient: Stream
    responseHandlers: ConcurrentDictionary<int, ProtocolMessage * (JsonElement -> ProtocolMessage)>
    receivedMessageLog: ProtocolMessage ConcurrentQueue
    pendingRequests: ConcurrentDictionary<int, ProtocolMessage>
    fileSystem: FileSystem
    config: ConnectionConfig
}

let pollingUntil timeout predicate = async {
    let initialSleep = TimeSpan.FromMilliseconds 1.
    let nextSleep s = min (TimeSpan.FromSeconds 1.) (TimeSpan.( * )(2., s))

    let mutable next = true
    let mutable result = true
    let mutable remainingTimeout = if Timeout.InfiniteTimeSpan = timeout then TimeSpan.MaxValue else timeout
    let mutable sleepTime = initialSleep

    while next do
        if predicate() then next <- false else
        if remainingTimeout <= TimeSpan.Zero then next <- false; result <- false else

        let actualSleepTime = min remainingTimeout sleepTime
        do! actualSleepTime.TotalMilliseconds |> int |> Async.Sleep
        sleepTime <- nextSleep sleepTime
        remainingTimeout <- remainingTimeout - sleepTime

    return result
}
let floatToTimeSpan (seconds: float<s>) = TimeSpan.FromSeconds <| float seconds
let clientWrite client actions = async {
    let {
        clientToServer = clientToServer
        responseHandlers = responseHandlers
        receivedMessageLog = logs
        pendingRequests = pendingRequests
        config = config
        fileSystem = fs
        } = client
    use output = MessageWriter.borrowStream clientToServer

    let mutable id = 1
    let writeNotification method ps =
        MessageWriter.writeJson output <| JsonRpcMessage.notification method ps

    let writeRequest message method ps parser =
        MessageWriter.writeJson output <| JsonRpcMessage.request id method ps
        responseHandlers.AddOrUpdate(id, (message, parser), fun _ v -> v) |> ignore
        Interlocked.Increment &id |> ignore

    let writeResponse id response =
        match response with
        | Ok r -> JsonRpcMessage.successResponse id r
        | Error e -> JsonRpcMessage.errorResponse id e
        |> MessageWriter.writeJson output

    let writeMessage m =
        match m with
        | Initialize x -> JsonElement.parse<_> >> InitializeResponse |> writeRequest m Methods.initialize (ValueSome x)
        | Initialized -> writeNotification Methods.initialized ValueNone
        | Shutdown -> (fun _ -> ShutdownResponse) |> writeRequest m Methods.shutdown ValueNone
        | Exit -> writeNotification Methods.exit ValueNone

        | DidOpen x -> writeNotification Methods.``textDocument/didOpen`` <| ValueSome x
        | DidChange x -> writeNotification Methods.``textDocument/didChange`` <| ValueSome x

        | DidChangeWatchedFiles x -> writeNotification Methods.``workspace/didChangeWatchedFiles`` <| ValueSome x
        | DidSave x -> writeNotification Methods.``textDocument/didSave`` <| ValueSome x

        | Hover x ->
            writeRequest m Methods.``textDocument/hover`` (ValueSome x) <| fun e ->
                JsonElement.parse<_> e |> HoverResponse

        | SemanticTokensFull x ->
            writeRequest m Methods.``textDocument/semanticTokens/full`` (ValueSome x) <| fun e ->
                JsonElement.parse e |> SemanticTokensFullResponse

        | SemanticTokensRange x ->
            writeRequest m Methods.``textDocument/semanticTokens/range`` (ValueSome x) <| fun e ->
                JsonElement.parse e |> SemanticTokensRangeResponse

        | HoverResponse _
        | ShutdownResponse _
        | InitializeResponse _
        | SemanticTokensFullResponse _
        | SemanticTokensRangeResponse _
            -> failwith $"invalid client to server response: %A{m}"

        | RegisterCapability _
            -> failwith $"invalid client to server request: %A{m}"

        | PublishDiagnostics _
            -> failwith $"invalid client to server notification: %A{m}"

        | RegisterCapabilityResponse
            -> failwithf "TODO: %A" m

    let polling timeout action predicate = async {
        let timeout = config.timeoutMap timeout
        let! success = pollingUntil timeout predicate
        if not success then failwith $"timeout; underlying action: %A{action}; messages: %A{logs}"
    }
    let processAction action = async {
        match action with
        | ReceiveRequest(handler, timeout) -> do! polling (Option.map floatToTimeSpan timeout |> Option.defaultValue Timeout.InfiniteTimeSpan) action <| fun () ->
            let r =
                pendingRequests
                |> Seq.tryPick (fun kv -> handler kv.Value |> Option.map (fun r -> kv.Key, r))

            match r with
            | Some(id, response) ->
                pendingRequests.TryRemove id |> ignore
                writeResponse id response
                true

            | _ -> false

        | WaitUntil(predicate, timeout) -> do! polling (Option.map floatToTimeSpan timeout |> Option.defaultValue Timeout.InfiniteTimeSpan) action <| fun () ->
            predicate <| Seq.toList logs

        | Sleep time -> do! floatToTimeSpan time |> Async.Sleep
        | WriteFile(path, contents) -> fs.writeAllText(path, contents)
        | Send m -> writeMessage m
    }
    let loop actions = async {
        let mutable actions = actions
        let mutable next = true
        while next do
            match actions with
            | [] -> next <- false
            | action::actions' ->
                do! processAction action
                actions <- actions'
    }
    do! loop actions
}
let clientRead { responseHandlers = responseHandlers; receivedMessageLog = logs; pendingRequests = pendingRequests; serverToClient = serverToClient } = async {
    let reader = MessageReader.borrowStream serverToClient

    let rec aux() =
        match MessageReader.read Utf8Serializable.protocolValue<JsonRpcMessage<JsonElement, Methods, JsonElement>> reader with
        | Ok x ->
            let m = parseMessage x
            let r =
                match m with
                | Notification r -> r

                | Request(id, r) ->
                    if not <| pendingRequests.TryAdd(id, r) then failwith $"duplicated request id: {id} %A{r}"
                    r

                | Response(id, r) ->
                    match responseHandlers.TryRemove id with
                    | false, _ -> failwith $"handler not found: %A{m}"
                    | _, (_, handler) -> handler r

            logs.Enqueue r
            aux()

        | Error MessageReader.ErrorKind.EndOfSource ->
            if not responseHandlers.IsEmpty then
                failwithf "require responses: %A, logs: %A" responseHandlers logs

            if not pendingRequests.IsEmpty then
                failwith $"unsent responses: %A{pendingRequests}"

        | Error x -> failwithf "message read error: %A %A" x reader
    aux()
}
let normalizeRegistrationParams x =
    { x with
        registrations =
            x.registrations
            |> Array.map (fun x ->
                { x with
                    id = ""
                }
            )
    }

let normalizeMessage = function
    | RegisterCapability x -> RegisterCapability <| normalizeRegistrationParams x
    | x -> x

let normalizeMessages = List.map normalizeMessage

let removeOldDiagnostics messages =
    let uriToLatestDiagnosticVersion =
        messages
        |> Seq.choose (function PublishDiagnostics d -> Some d | _ -> None)
        |> Seq.groupBy (fun d -> d.uri)
        |> Seq.map (fun (uri, ds) ->
            uri, ds |> Seq.map (fun d -> d.version) |> Seq.max
        )
        |> Map.ofSeq

    messages
    |> List.filter (function
        | PublishDiagnostics d -> uriToLatestDiagnosticVersion.[d.uri] = d.version
        | _ -> true
    )
    |> List.map (function
        | PublishDiagnostics d -> PublishDiagnostics { d with version = Undefined }
        | x -> x
    )

let serverActionsWithBoilerPlate withConfig actions = async {
    let config = withConfig ConnectionConfig.defaultValue
    let writeTimeout = config.timeoutMap(config.writeTimeout).TotalMilliseconds |> int
    let readTimeout = config.timeoutMap(config.readTimeout).TotalMilliseconds |> int

    use clientToServer = new BlockingStream(ReadTimeout = readTimeout, WriteTimeout = writeTimeout)
    use serverToClient = new BlockingStream(ReadTimeout = readTimeout, WriteTimeout = writeTimeout)

    let fileSystem = config.createFileSystem()
    for f in config.globalModuleFiles do
        fileSystem.writeAllText(DocumentPath.ofPath (Path.GetFullPath f.path), f.source)

    for f in config.initialFiles do
        fileSystem.writeAllText(DocumentPath.ofRelativeUri config.rootUri (Uri(f.uri, UriKind.RelativeOrAbsolute)), f.source)

    let server = async {
        let reader = MessageReader.borrowStream clientToServer
        use writer = MessageWriter.borrowStream serverToClient
        (reader, writer)
        |> Server.start (fun c ->
            { c with
                fileSystem = fileSystem
                platform = config.serverPlatform
                resourcePaths = ["./resources.xml"]
                backgroundCheckDelay = config.backgroundCheckDelay
                globalModulePaths = [for f in config.globalModuleFiles do f.path]
            }
        )
        serverToClient.CompleteWriting()
    }
    let client = {
        responseHandlers = ConcurrentDictionary()
        receivedMessageLog = ConcurrentQueue()
        pendingRequests = ConcurrentDictionary()
        clientToServer = clientToServer
        serverToClient = serverToClient
        fileSystem = fileSystem
        config = config
    }
    do! Async.ParallelAction [
        server
        async {
            do! clientWrite client actions
            clientToServer.CompleteWriting()
        }
        clientRead client
    ]
    let messages = Seq.toList client.receivedMessageLog
    let messages = normalizeMessages messages
    return messages
}
let receiveRequest timeout f = ReceiveRequest(f >> Option.map Ok, Some timeout)
let waitUntilExists timeout predicate = WaitUntil(List.exists predicate, Some timeout)
let waitUntilHasDiagnosticsOf targetUri = waitUntilExists 5.<_> <| function
    | PublishDiagnostics { uri = uri } -> uri = targetUri
    | _ -> false

let waitUntilMatchLatestDiagnosticsOf fileUri predicate =
    let predicate ms =
        ms
        |> Seq.choose (function PublishDiagnostics d when fileUri = d.uri -> Some d | _ -> None)
        |> Seq.sortByDescending (fun d -> d.version)
        |> Seq.tryHead
        |> Option.map (fun d -> predicate d.diagnostics)
        |> Option.defaultValue false

    WaitUntil(predicate, Some 5.<_>)

let serverActions withConfig messages = async {
    let config = withConfig ConnectionConfig.defaultValue
    let! rs = serverActionsWithBoilerPlate withConfig [
        Send <| Initialize { rootUri = ValueSome config.rootUri }
        waitUntilExists 5.<_> <| function
            | InitializeResponse _ -> true
            | _ -> false
        Send Initialized
        receiveRequest 5.<_> <| function
            | RegisterCapability _ -> Some RegisterCapabilityResponse
            | _ -> None
        yield! messages
        Send Shutdown
        waitUntilExists 5.<_> <| function
            | ShutdownResponse -> true
            | _ -> false
        Send Exit
    ]
    match rs with
    | InitializeResponse _::RegisterCapability _::rs when List.last rs = ShutdownResponse -> return rs.[..List.length rs-2]
    | _ -> return failwithf "%A" rs
}


let range (sl, sc) (el, ec) = {
    start = { line = sl; character = sc }
    ``end`` = { line = el; character = ec }
}
let diagnostic severity (sl, sc) (el, ec) code message = {
    range = range (sl, sc) (el, ec)
    severity = Defined severity
    code = Defined code
    source = ""
    message = message
    tags = Undefined
    relatedInformation = Undefined
}

let error = diagnostic DiagnosticSeverity.Error
let warning = diagnostic DiagnosticSeverity.Warning
let info = diagnostic DiagnosticSeverity.Information

let didChange changes (path, version) = Send <| DidChange {
    textDocument = {
        uri = Uri path
        version = ValueSome version
    }
    contentChanges = [|
        for range, text in changes do {
            range = range |> Option.map Defined |> Option.defaultValue Undefined
            text = text
        }
    |]
}
let didChangeFull newSource (path, version) = Send <| DidChange {
    textDocument = {
        uri = Uri path
        version = ValueSome version
    }
    contentChanges = [|
        { range = Undefined; text = newSource }
    |]
}
let didSave path = Send <| DidSave {
    textDocument = {
        uri = Uri path
    }
}
/// `WriteFile(…)`
let (?>) source uri = WriteFile(DocumentPath.ofUri (Uri uri), source)
let didChangeWatchedFiles changes = Send <| DidChangeWatchedFiles { changes = [|
    for path, changeType in changes do { uri = Uri path; ``type`` = changeType }
|]}
let publishDiagnosticsParams uri diagnostics = {
    uri = uri
    version = Undefined
    diagnostics = Seq.toArray diagnostics
}
let publishDiagnostics uri version diagnostics = PublishDiagnostics {
    publishDiagnosticsParams uri diagnostics with
        version = Defined version
}
let sortDiagnosticsAndOthers messages =
    let isDiagnostics = function
        | PublishDiagnostics _ -> true
        | _ -> false

    let others = List.filter (isDiagnostics >> not) messages
    let diagnostics =
        messages
        |> List.filter isDiagnostics
        |> List.sortBy (function PublishDiagnostics d -> d.version | _ -> failwith "")

    diagnostics, others

type TestsFixture() =
    let mutable outputLogger = None

    member _.SetOutput(output: ITestOutputHelper) =
        match outputLogger with
        | None ->
            let logger = { new Logger() with
                member _.Log e = output.WriteLine("[{0:O}] {1} : {2} : {3}", e.time, e.source, e.level, e.message)
            }
            outputLogger <- Some logger
            Logger.add Log.logger logger

        | _ -> ()

    interface IDisposable with
        member _.Dispose() =
            outputLogger |> Option.iter (Logger.remove Log.logger)

let semanticTokenFullResponseData source = async {
    let! r = serverActions id [
        source &> ("file:///main.lua", 1)
        waitUntilHasDiagnosticsOf "file:///main.lua"
        Send <| SemanticTokensFull { SemanticTokensParams.textDocument = { uri = Uri "file:///main.lua" } }
        waitUntilExists 5.<_> <| function
            | SemanticTokensFullResponse _ -> true
            | _ -> false
    ]
    match List.last r with
    | SemanticTokensFullResponse(ValueSome { data = data }) -> return data
    | _ -> return failwith $"%A{r}"
}
