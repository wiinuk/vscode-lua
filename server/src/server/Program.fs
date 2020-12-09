module LuaChecker.Server.Program
open LuaChecker
open LuaChecker.Primitives
open LuaChecker.Server
open LuaChecker.Server.Server
open LuaChecker.Server.Json
open LuaChecker.Server.Protocol
open LuaChecker.Server.Log
open LuaChecker.Text.Json
open LuaChecker.Text.Json.Parsing
open System
open System.Collections.Concurrent
open System.Text
open System.Text.Json


type private M = LuaChecker.Server.Protocol.Methods
module Server = Server.Interfaces

let options = ParserOptions.createFromParsers [
    FSharpRecordParserFactory()
    FSharpOptionParserFactory()
    FSharpValueOptionParserFactory()
    FSharpRecordOptionalFieldParserFactory()
    FSharpUnitParser()
]

let parse<'T> e = JsonElementParser.parse<'T> options e

let processNotification server ps = function
    | M.initialized -> Server.initialized server
    | M.``textDocument/didOpen`` -> Server.didOpenTextDocument server <| parse<_> ps
    | M.``textDocument/didChange`` -> Server.didChangeTextDocument server <| parse<_> ps
    | M.``textDocument/didClose`` -> Server.didCloseTextDocument server <| parse<_> ps

    //| M.``workspace/didChangeConfiguration`` -> Server.didChangeConfiguration server ps
    | M.``textDocument/didSave`` -> Server.didSaveTextDocument server <| parse<_> ps
    | M.``workspace/didChangeWatchedFiles`` -> Server.didChangeWatchedFiles server <| parse<_> ps

    | method -> ifWarn { Log.Format(server.resources.LogMessages.UnknownNotification, method, ps) }; Async.completed

let inline wrapJsonInOut serverMethod ps id = async {
    let! r = serverMethod (parse<_> ps)
    return serializeJsonRpcResponse id r
}

let processRequest server id ps = function
    | M.initialize -> Server.initialize server id <| parse ps

    | M.``textDocument/hover`` -> Server.hover server id <| parse ps
    //| M.``workspace/didChangeWorkspaceFolders`` ->

    | M.shutdown -> Server.shutdown server id <| parse ps

    | method ->
        ifError { Log.Format(server.resources.LogMessages.UnknownRequest, id, method, ps) }
        Server.putResponseTask server id <| async.Return ReadOnlyMemory.Empty

let processSuccessResponse server id result =
    let mutable handler = Unchecked.defaultof<_>
    if server.requestIdToHandler.TryRemove(id, &handler) then
        handler result
    else
        ifWarn { Log.Format(server.resources.LogMessages.ResponseHandlerNotFound, id, result) }

let processErrorResponse server id error =
    ifError { Log.Format(server.resources.LogMessages.ErrorResponseReceived, id, OptionalField.toOption error) }

let (?) (json: JsonElement) (name: string) = json.GetProperty name

let processMessage server = function
    | { JsonRpcMessage.method = Defined M.``$/cancelRequest``; ``params`` = Defined ps } ->
        let id = ps?id.GetInt32()

        let mutable cancel = null
        if server.pipe.pendingRequests.TryGetValue(id, &cancel) then
            cancel.Cancel()
            ifInfo { Log.Format(server.resources.LogMessages.RequestCanceled, id) }

    | { id = Undefined; method = Defined method; ``params`` = ps } ->
        let ps = OptionalField.defaultValue (JsonElement()) ps
        let task = processNotification server ps method
        server.pipe.messageQueue.Add(Notification(method, task))

    | { id = Defined id; method = Defined method; ``params`` = json } ->
        let json = OptionalField.defaultValue (JsonElement()) json
        processRequest server id json method

    | { id = Defined id; result = Defined result } ->
        processSuccessResponse server id result

    | { id = Defined id; result = Undefined; error = error } ->
        processErrorResponse server id error

    | message ->
        ifInfo { Log.Format(server.resources.LogMessages.InvalidMessageFormat, message) }

let processMessages server =
    let rec aux() =
        let r =
            try MessageReader.read Utf8Serializable.protocolValue<JsonRpcMessage<JsonElement, Methods, JsonElement>> server.input
            with :? JsonException -> Error MessageReader.ErrorKind.DeserializeFailure

        match r with
        | Error MessageReader.ErrorKind.EndOfSource -> ()
        | Error MessageReader.ErrorKind.RequireContentLengthHeader -> ifWarn { trace "Message was ignored." }; aux()
        | Error MessageReader.ErrorKind.DeserializeFailure -> ifWarn { trace "JSON RPC format is invalid." }; aux()
        | Error e -> ifError { Log.Format(server.resources.LogMessages.MessageParseError, e) }
        | Ok { method = Defined M.exit } -> ifInfo { Log.Format server.resources.LogMessages.ReceivedExitNotification }
        | Ok request ->
            ifDebug { Log.Format(server.resources.LogMessages.MessageReceived, request) }
            processMessage server request
            aux()
    aux()
    server.pipe.messageQueue.Add Quit

let backgroundWorker server = async {
    do! Async.SwitchToNewThread()
    try processMessages server
    with e -> ifError { trace "%A" e }
}

let receiveMessages server =
    let rec aux() =
        match server.pipe.messageQueue.Take() with
        | Quit -> ()
        | Notification(_, task) -> Async.RunSynchronously task; aux()
        | Response(id, task, cancel) ->
            try
                let response = Async.RunSynchronously(task, 0, cancel.Token)
                ifDebug { Log.Format(server.resources.LogMessages.ResponseSending, Encoding.UTF8.GetString response.Span) }
                MessageWriter.writeUtf8 server.output response.Span

            with :? OperationCanceledException ->
                ifInfo { Log.Format(server.resources.LogMessages.RequestCanceled, id) }

            aux()
    aux()

let connect server =
    backgroundWorker server |> Async.Start
    receiveMessages server

[<EntryPoint>]
let main _ =
    let input = MessageReader.borrowStream <| Console.OpenStandardInput()
    use output = MessageWriter.borrowStream <| Console.OpenStandardOutput()
    use messageQueue = new BlockingCollection<_>(8)
    let server = Server.create id (input, output, messageQueue)
    try
        ifInfo { trace "%s" server.resources.LogMessages.ServerStarting }
        connect server
        ifInfo { trace "%s" server.resources.LogMessages.ServerTerminatedNormally }
        0
    with e ->
        ifError { trace "%A" e }
        1
