module LuaChecker.Server.Test.Helpers
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
    | Sleep of TimeSpan
    | WriteFile of path: DocumentPath * contents: string
    | WhenMessages of predicate: (ProtocolMessage list -> bool) * timeout: TimeSpan option

let (&>) source (path, version) = Send <| DidOpen {
    textDocument = {
        text = source
        uri = Uri path
        version = version
    }
}

type ResponseError = {
    code: double
    message: string
    data: JsonElement OptionalField
}
type JsonRpcMessage = {
    jsonrpc: JsonRpcVersion
    id: int OptionalField
    result: JsonElement OptionalField
    error: ResponseError OptionalField
    method: Methods OptionalField
    ``params``: JsonElement OptionalField
}
let parse popHandler handlers x =
    match x.method with
    | Defined m ->
        match x.id with

        // request
        | Defined _ ->
            failwithf "TODO: request: %A" x

        // notification
        | _ ->
            let x =
                match m, x.``params`` with
                | Methods.``textDocument/publishDiagnostics``, Defined ps ->
                    PublishDiagnostics <| Program.parse<PublishDiagnosticsParams> ps

                | _ -> failwithf "TODO: notification: %A" x

            x, handlers
    | _ ->

        // response
        match x.id with
        | Undefined -> failwithf "require id: %A" x

        | Defined id ->

        match popHandler id handlers with
        | None -> failwithf "id out of range: %d %A" id x
        | Some((_, p), parsers) ->

        match x.result with
        | Undefined -> failwithf "response with error: %A" x
        | Defined ps -> p ps, parsers

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
type Client<'K,'V,'L,'C,'F> = {
    clientToServer: Stream
    serverToClient: Stream
    responseHandlers: ConcurrentDictionary<'K,'V>
    logs: 'L ConcurrentQueue
    fileSystem: 'F
    config: 'C
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
let clientWrite client actions = async {
    let {
        clientToServer = clientToServer
        responseHandlers = responseHandlers
        logs = logs
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

    let writeMessage m =
        match m with
        | Initialize x -> Program.parse<_> >> InitializeResponse |> writeRequest m Methods.initialize (Defined x)
        | Initialized -> writeNotification Methods.initialized Undefined
        | Shutdown -> (fun _ -> ShutdownResponse) |> writeRequest m Methods.shutdown Undefined
        | Exit -> writeNotification Methods.exit Undefined

        | DidOpen x -> writeNotification Methods.``textDocument/didOpen`` <| Defined x
        | DidChange x -> writeNotification Methods.``textDocument/didChange`` <| Defined x

        | DidChangeWatchedFiles x -> writeNotification Methods.``workspace/didChangeWatchedFiles`` <| Defined x
        | DidSave x -> writeNotification Methods.``textDocument/didSave`` <| Defined x

        | Hover x ->
            writeRequest m Methods.``textDocument/hover`` (Defined x) (fun e ->
                Program.parse<_> e |> HoverResponse
            )

        | HoverResponse _
            -> failwith $"invalid client response: %A{m}"

        | InitializeResponse _
        | PublishDiagnostics _
        | ShutdownResponse _
            -> failwithf "TODO: %A" m

    let processAction action = async {
        match action with
        | WhenMessages(predicate, timeout) ->
            let timeout = Option.map config.timeoutMap timeout
            let! success = pollingUntil timeout <| fun () -> predicate <| Seq.toList logs
            if not success then failwithf "timeout; action: %A; messages: %A" action logs

        | Sleep time -> do! Async.Sleep time
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
let clientRead { responseHandlers = responseHandlers; logs = logs; serverToClient = serverToClient } = async {
    let pop k (d: ConcurrentDictionary<_,_>) =
        let mutable r = Unchecked.defaultof<_>
        if d.TryRemove(k, &r) then Some(r, d) else None

    let reader = MessageReader.borrowStream serverToClient

    let rec aux() =
        match MessageReader.read Utf8Serializable.protocolValue<JsonRpcMessage> reader with
        | Ok x ->
            let x, _ = parse pop responseHandlers x
            logs.Enqueue x
            aux()

        | Error MessageReader.ErrorKind.EndOfSource ->
            if not responseHandlers.IsEmpty then
                failwithf "require responses: %A" responseHandlers

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

    let server = async {
        let reader = MessageReader.borrowStream clientToServer
        use writer = MessageWriter.borrowStream serverToClient
        let server =
            (reader, writer)
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
        logs = ConcurrentQueue()
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
    return Seq.toList client.logs
}
let serverActions withConfig messages = async {
    let! rs = serverActionsWithBoilerPlate withConfig [
        Send <| Initialize { rootUri = ValueSome(Uri "file:///") }
        Send Initialized
        yield! messages
        Send Shutdown
        Send Exit
    ]
    match List.head rs, List.last rs with
    | InitializeResponse _, ShutdownResponse -> return rs.[1 .. List.length rs-2]
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
