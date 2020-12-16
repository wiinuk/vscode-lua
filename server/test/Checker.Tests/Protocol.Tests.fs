module LuaChecker.Server.Protocol.Tests
open FsCheck
open LuaChecker
open LuaChecker.Checker.Test.Utils
open LuaChecker.Primitives
open LuaChecker.Server
open LuaChecker.Server.Protocol
open LuaChecker.Text.Json
open System
open System.IO
open System.Text
open System.Text.Json.Serialization
open Xunit
type ErrorKind = MessageReader.ErrorKind


let u8ToString u8 = Encoding.UTF8.GetString(u8: _ array)
let u8 s = Encoding.UTF8.GetBytes(s = s)
let toProtocol json = Array.concat [
    u8"Content-Length: "; u8(string <| Array.length json); u8"\n"
    u8"\n"
    json
]

type Params =
    | None = 0
    | ``Good afternoon`` = 1
    | ``How are you?`` = 2
    | ``How do you do`` = 3
    | ``Nice to meet you.`` = 4
    | Hello = 5
    | Goodbye = 6

[<JsonConverter(typeof<JsonStringEnumConverter>)>]
type Methods =
    | Unknown = 0
    | greeting = 1
    | upper = 2
    | paint = 3
    | echo = 4
    | length = 5

type Utf8JsonSerializable<'T> = struct
    interface IUtf8SerializableShape<'T> with
        override _.Deserialize x = Json.deserialize<_> x
end
let utf8JsonSerializable<'T> = the<Utf8JsonSerializable<'T>>

[<Fact>]
let readSimpleMessage() =
    let input = new MemoryStream()
    let reader = MessageReader.borrowStream input

    let m = toProtocol @"{""jsonrpc"":""2.0"",""method"":""greeting"",""params"":5}"B
    input.Write(ReadOnlySpan m)
    input.Position <- 0L

    MessageReader.read utf8JsonSerializable reader =? Ok (JsonRpcMessage.notification Methods.greeting (ValueSome Params.Hello))
    MessageReader.read utf8JsonSerializable reader =? Error ErrorKind.EndOfSource
    MessageReader.read utf8JsonSerializable reader =? Error ErrorKind.EndOfSource

let messageRoundTripProperty message =
    let source = toProtocol <| Json.serialize message

    sprintf "source: %A" (u8ToString source) @| lazy

    let input = new MemoryStream(source, writable = false)

    let reader = MessageReader.borrowStream input
    MessageReader.read utf8JsonSerializable reader =? Ok message
    MessageReader.read utf8JsonSerializable reader =? Error ErrorKind.EndOfSource
    MessageReader.read utf8JsonSerializable reader =? Error ErrorKind.EndOfSource

[<Fact>]
let messageRoundTrip() = check <| fun x ->
    let x: JsonRpcMessage<Params, Methods, Params> =
        match x with
        | Choice1Of4(m, ps) -> JsonRpcMessage.notification m ps
        | Choice2Of4(id, m, ps) -> JsonRpcMessage.request id m ps
        | Choice3Of4(id, r) -> JsonRpcMessage.successResponse id r
        | Choice4Of4(id, e) ->
            e
            |> Option.map (fun (code, NonNull message) ->
                { code = code; message = message; data = Undefined }
            )
            |> Option.unbox
            |> JsonRpcMessage.errorResponse id

    messageRoundTripProperty x

[<Fact>]
let serializeJsonRpcVersion() =
    JsonRpcVersion.``2.0``
    |> Json.serializeString =? "\"2.0\""

[<Fact>]
let writeSimpleResponse() =
    use m = new MemoryStream()
    use w = MessageWriter.borrowStream m
    MessageWriter.writeUtf8 w (ReadOnlySpan(u8"""ABCD"""))
    m.ToArray() |> u8ToString =? "Content-Length: 4\r\n\r\nABCD"

[<Fact>]
let writeSimpleMessage() =
    let message = {
        jsonrpc = JsonRpcVersion.``2.0``
        id = Defined 10
        method = Defined Methods.``textDocument/publishDiagnostics``
        ``params`` = Defined {
            uri = "A:/dir/file.ext"
            version = Undefined
            diagnostics = [|
                {
                    severity = Defined DiagnosticSeverity.Information
                    range = {
                        start = { line = 0; character = 1 }
                        ``end`` = { line = 2; character = 3 }
                    }
                    code = Defined 30
                    source = "source text"
                    message = "message text"
                    tags = Undefined
                    relatedInformation = Undefined
                }
            |]
        }
        result = Undefined
        error = Undefined
    }
    let expected = "Content-Length: 266\r\n\r\n" + """{"jsonrpc":"2.0","id":10,"method":"textDocument/publishDiagnostics","params":{"uri":"A:/dir/file.ext","diagnostics":[{"range":{"start":{"line":0,"character":1},"end":{"line":2,"character":3}},"severity":3,"code":30,"source":"source text","message":"message text"}]}}"""

    use m = new MemoryStream()
    use w = MessageWriter.borrowStream m
    MessageWriter.writeJson w message
    m.ToArray() |> u8ToString =? expected

let writerToReaderMessageRoundTripProperty idAndParams =
    use m = new MemoryStream()
    use w = MessageWriter.borrowStream m

    let expectedMessages =
        idAndParams
        |> List.map (fun (PositiveInt id, ``params``) ->
            JsonRpcMessage.request id
                Methods.``textDocument/publishDiagnostics``
                (ValueSome(``params``: PublishDiagnosticsParams))
        )

    for m in expectedMessages do MessageWriter.writeJson w m

    m.Position <- 0L
    let r = MessageReader.borrowStream m

    let actualMessages = [
        let mutable next = true
        while next do
            match MessageReader.read utf8JsonSerializable r with
            | Error ErrorKind.EndOfSource -> next <- false
            | Error e -> failwithf "%A, position: %d, source: `%s`" e m.Position <| u8ToString (m.ToArray())
            | Ok x -> yield x
    ]
    actualMessages =? expectedMessages

[<Fact>]
let writerToReaderMessageRoundTrip() = check writerToReaderMessageRoundTripProperty

[<Fact>]
let doubleMessageRoundTrip() = writerToReaderMessageRoundTripProperty [
    PositiveInt 1,
    {
        uri = "a"
        version = Defined 1
        diagnostics = [||]
    }
    PositiveInt 2,
    {
        uri = "a"
        version = Defined 2
        diagnostics = [||]
    }
]

[<Fact>]
let writeOptionalField() = writerToReaderMessageRoundTripProperty [
    PositiveInt 1, {
        uri = ""
        version = Defined 1
        diagnostics = [|
            {
            range = {
                start = { line = 0; character = 0 }
                ``end`` = { line = 0; character = 0 }
            }
            severity = Undefined
            code = Undefined
            source = ""
            message = ""
            tags = Undefined
            relatedInformation = Defined [||]
            }
        |]
    }
]

[<Fact>]
let documentPathRoundTrip() =
    let roundTripTest expected =
        let source = DocumentPath.ofUri expected
        let actual = DocumentPath.toUri source
        actual =? expected

    roundTripTest <| Uri "file:///C:/dir/file.ext"

[<Fact>]
let escapedDocumentPath() =
    let d = DocumentPath.ofUri (Uri "file:///c%3A/dir/file.ext")
    d =? DocumentPath.ofUri (DocumentPath.toUri d)

[<Fact>]
let pathToDocumentPathRoundTrip() =
    let absolutePath = Environment.CurrentDirectory

    DocumentPath.ofUri (Uri absolutePath)
    |> DocumentPath.toPathOrFail =? absolutePath
