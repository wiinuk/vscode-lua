module LuaChecker.Server.Protocol.MessageReader
open LuaChecker.Primitives
open System
open System.Buffers
open System.Buffers.Text
open System.IO


[<Struct; RequireQualifiedAccess>]
type Header =
    | End
    | ContentLength of int
    | Unknown

type ErrorKind =
    | EndOfSource = 0uy
    | ContentLengthMismatch = 1uy
    | RequireContentLengthHeader = 2uy
    | DeserializeFailure = 3uy

type private E = ErrorKind

type MessageReader = {
    source: Stream
    buffer: byte ArrayBufferWriter
}

let borrowStream source = {
    source = source
    buffer = ArrayBufferWriter()
}

let rec readLine (utf8Buffer: _ ArrayBufferWriter) (source: Stream) =
    match source.ReadByte() with
    | -1 -> 0 < utf8Buffer.WrittenCount
    | c ->

    match byte c with
    | '\n'B -> true
    | '\r'B ->
        match source.ReadByte() with

        // …\r
        | -1 -> 0 < utf8Buffer.WrittenCount

        | c ->

        match byte c with

        // …\r\n…
        | '\n'B -> true

        // …\r□…
        | c ->
            utf8Buffer.GetSpan(1).[0] <- c
            utf8Buffer.Advance 1
            readLine utf8Buffer source

    // …□…
    | c ->
        utf8Buffer.GetSpan(1).[0] <- c
        utf8Buffer.Advance 1
        readLine utf8Buffer source

let private utf8ContentLengthHeaderHead = "Content-Length: "B
let parseHeader (line: _ ReadOnlySpan) =
    if line.IsEmpty then Header.End
    elif line.StartsWith(ReadOnlySpan utf8ContentLengthHeaderHead) then
        let line' = line.Slice utf8ContentLengthHeaderHead.Length
        let mutable result = 0
        let mutable bytesConsumed = 0
        if Utf8Parser.TryParse(line', &result, &bytesConsumed) && bytesConsumed = line'.Length then
            Header.ContentLength result
        else
            Header.Unknown
    else
        Header.Unknown

let rec skipWhiteSpaces (input: Stream) =
    match input.ReadByte() with
    | -1 -> Error E.ContentLengthMismatch
    | c ->

    match byte c with
    | '\t'B
    | '\n'B
    | '\v'B
    | '\r'B
    | ' 'B -> skipWhiteSpaces input
    | c -> Ok c

let readBytes (buffer: _ Span) (source: Stream) =
    let mutable remaining = buffer
    while
        match source.Read remaining with
        | 0 -> false
        | readCount ->
            remaining <- remaining.Slice readCount
            0 < remaining.Length
        do ()
    buffer.Length - remaining.Length

let readBody _s contentLength { buffer = buffer; source = source } =
    if contentLength = 0 then Ok <| Utf8Serializable.deserialize _s ReadOnlySpan.Empty else

    match skipWhiteSpaces source with
    | Error e -> Error e
    | Ok c0 ->

    buffer.Clear()
    let contents = buffer.GetSpan(contentLength).Slice(0, contentLength)
    contents.[0] <- c0

    let tail = contents.Slice 1
    let readLength = readBytes tail source
    if readLength < tail.Length then Error E.ContentLengthMismatch else

    Ok <| Utf8Serializable.deserialize _s (Span.op_Implicit contents)

[<Struct>]
type PartialHeaders = {
    contentLength: int voption
}
module PartialHeaders =
    let create() = { contentLength = ValueNone }

let rec readMessage _s headers ({ buffer = buffer; source = source } as reader) =
    buffer.Clear()
    if readLine buffer source then
        match parseHeader buffer.WrittenSpan with
        | Header.ContentLength x -> readMessage _s { headers with contentLength = ValueSome x } reader
        | Header.Unknown -> readMessage _s headers reader
        | Header.End ->

        match headers.contentLength with
        | ValueNone -> Error E.RequireContentLengthHeader
        | ValueSome x ->

        match readBody _s x reader with
        | Error e -> Error e
        | Ok x -> Ok x
    else
        Error E.EndOfSource

let read _s reader = readMessage _s (PartialHeaders.create()) reader
