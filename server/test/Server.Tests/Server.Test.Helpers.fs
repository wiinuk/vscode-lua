module LuaChecker.Server.Test.Helpers
open FSharp.Data.UnitSystems.SI.UnitSymbols
open LuaChecker
open LuaChecker.Server
open LuaChecker.Server.Json
open LuaChecker.Server.Protocol
open LuaChecker.Text.Json
open System
open System.Collections.Concurrent
open System.Diagnostics
open System.IO
open System.Text.Json
open System.Threading


let (=?) l r = if not (l = r) then failwithf "%A =? %A" l r

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
                RegisterCapability <| Server.parse<RegistrationParams> ps

            | _ -> failwith $"TODO: request: %A{x}"

        Request(id, request)

    // notification
    | { method = Defined m; id = Undefined; ``params`` = ps } ->
        let x =
            match m, ps with
            | Methods.``textDocument/publishDiagnostics``, Defined ps ->
                PublishDiagnostics <| Server.parse<PublishDiagnosticsParams> ps

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
}
module ConnectionConfig =
    let defaultValue = {
        readTimeout = TimeSpan.FromSeconds 5.
        writeTimeout = TimeSpan.FromSeconds 5.
        timeoutMap = fun x -> if Debugger.IsAttached then Timeout.InfiniteTimeSpan else x
        backgroundCheckDelay = TimeSpan.Zero
        serverPlatform = Some PlatformID.Win32NT
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
    let mutable remainingTimeout = timeout |> Option.defaultValue TimeSpan.MaxValue
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
        | Initialize x -> Server.parse<_> >> InitializeResponse |> writeRequest m Methods.initialize (ValueSome x)
        | Initialized -> writeNotification Methods.initialized ValueNone
        | Shutdown -> (fun _ -> ShutdownResponse) |> writeRequest m Methods.shutdown ValueNone
        | Exit -> writeNotification Methods.exit ValueNone

        | DidOpen x -> writeNotification Methods.``textDocument/didOpen`` <| ValueSome x
        | DidChange x -> writeNotification Methods.``textDocument/didChange`` <| ValueSome x

        | DidChangeWatchedFiles x -> writeNotification Methods.``workspace/didChangeWatchedFiles`` <| ValueSome x
        | DidSave x -> writeNotification Methods.``textDocument/didSave`` <| ValueSome x

        | Hover x ->
            writeRequest m Methods.``textDocument/hover`` (ValueSome x) (fun e ->
                Server.parse<_> e |> HoverResponse
            )

        | HoverResponse _
        | ShutdownResponse _
        | InitializeResponse _
            -> failwith $"invalid client to server response: %A{m}"

        | RegisterCapability _
            -> failwith $"invalid client to server request: %A{m}"

        | PublishDiagnostics _
            -> failwith $"invalid client to server notification: %A{m}"

        | RegisterCapabilityResponse
            -> failwithf "TODO: %A" m

    let polling timeout action predicate = async {
        let timeout = Option.map config.timeoutMap timeout
        let! success = pollingUntil timeout predicate
        if not success then failwith $"timeout; underlying action: %A{action}; messages: %A{logs}"
    }
    let processAction action = async {
        match action with
        | ReceiveRequest(handler, timeout) -> do! polling (Option.map floatToTimeSpan timeout) action <| fun () ->
            let r =
                pendingRequests
                |> Seq.tryPick (fun kv -> handler kv.Value |> Option.map (fun r -> kv.Key, r))

            match r with
            | Some(id, response) ->
                pendingRequests.TryRemove id |> ignore
                writeResponse id response
                true

            | _ -> false

        | WaitUntil(predicate, timeout) -> do! polling (Option.map floatToTimeSpan timeout) action <| fun () ->
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

let copyTextFilesFromRealFileSystem fileSystem paths =
    let paths = [
        for path in paths do
            let path = System.Uri(Path.GetFullPath(Path.Combine(System.Environment.CurrentDirectory, path)))
            DocumentPath.ofUri (System.Uri "file:///") path
    ]
    for path in paths do
        fileSystem.writeAllText(path, File.ReadAllText(DocumentPath.toLocalPath path))

let serverActionsWithBoilerPlate withConfig actions = async {
    let config = withConfig ConnectionConfig.defaultValue
    let writeTimeout = config.timeoutMap(config.writeTimeout).TotalMilliseconds |> int
    let readTimeout = config.timeoutMap(config.readTimeout).TotalMilliseconds |> int

    use clientToServer = new BlockingStream(ReadTimeout = readTimeout, WriteTimeout = writeTimeout)
    use serverToClient = new BlockingStream(ReadTimeout = readTimeout, WriteTimeout = writeTimeout)

    let fileSystem = FileSystem.memory()
    let globalModulePaths = Server.ServerCreateOptions.defaultOptions.globalModulePaths
    copyTextFilesFromRealFileSystem fileSystem globalModulePaths

    use messageQueue = new BlockingCollection<_>(8)
    let server = async {
        let reader = MessageReader.borrowStream clientToServer
        use writer = MessageWriter.borrowStream serverToClient
        let server =
            (reader, writer, messageQueue)
            |> Server.create (fun c ->
                { c with
                    fileSystem = fileSystem
                    platform = config.serverPlatform
                    resourcePaths = ["./resources.xml"]
                    backgroundCheckDelay = config.backgroundCheckDelay
                    globalModulePaths = globalModulePaths
                }
            )
        Program.connect server
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
    return Seq.toList client.receivedMessageLog
}
let receiveRequest timeout f = ReceiveRequest(f >> Option.map Ok, Some timeout)
let serverActions withConfig messages = async {
    let! rs = serverActionsWithBoilerPlate withConfig [
        Send <| Initialize { rootUri = ValueSome(Uri "file:///") }
        Send Initialized
        receiveRequest 5.<_> <| function
            | RegisterCapability _ -> Some RegisterCapabilityResponse
            | _ -> None
        yield! messages
        Send Shutdown
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
let writeFile source path = WriteFile(DocumentPath.ofUri null (Uri path), source)
let didChangeWatchedFiles changes = Send <| DidChangeWatchedFiles { changes = [|
    for path, changeType in changes do { uri = Uri path; ``type`` = changeType }
|]}

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

let waitUntilExists timeout predicate = WaitUntil(List.exists predicate, Some timeout)
