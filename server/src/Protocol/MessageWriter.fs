module LuaChecker.Server.Protocol.MessageWriter
open LuaChecker.Server
open System
open System.IO
open System.Text
open System.Buffers
open System.Buffers.Text
open System.Runtime.CompilerServices
open System.Text.Json


type MessageWriter = {
    outputBuffer: byte ArrayBufferWriter
    output: Stream

    writerBuffer: byte ArrayBufferWriter
    writer: Utf8JsonWriter
}
with
    interface IDisposable with
        override w.Dispose() = w.writer.Dispose()

let borrowStream output =
    let writerBuffer = ArrayBufferWriter()
    let options = Json.options
    let options = JsonWriterOptions(Encoder = options.Encoder, Indented = options.WriteIndented, SkipValidation = true)
    {
        outputBuffer = ArrayBufferWriter()
        output = output

        writerBuffer = writerBuffer
        writer = new Utf8JsonWriter(writerBuffer, options)
    }
let utf8 = Encoding.UTF8
let utf8Memory (s: string) = utf8.GetBytes s |> ReadOnlyMemory

/// `"Content-Length: "`
let private utf8ContentLengthHeaderHead = "Content-Length: "B

[<Extension; Sealed; AbstractClass>]
type BufferWriterExtensions =
    [<Extension>]
    static member Write(writer: _ ArrayBufferWriter, value: int) =
        let mutable bytesWritten = 0
        if Utf8Formatter.TryFormat(value, writer.GetSpan 11, &bytesWritten)
        then writer.Advance bytesWritten
        else writer.Write(ReadOnlySpan(utf8.GetBytes(value.ToString())))

/// `"\r\n\r\n"`
let private utf8HeaderEnd = "\r\n\r\n"B
let writeUtf8 { outputBuffer = buffer; output = output } (utf8Message: _ ReadOnlySpan) =
    buffer.Clear()
    buffer.Write(ReadOnlySpan utf8ContentLengthHeaderHead)
    buffer.Write utf8Message.Length
    buffer.Write(ReadOnlySpan utf8HeaderEnd)
    output.Write buffer.WrittenSpan
    output.Write utf8Message

let writeJson { outputBuffer = outputBuffer; writer = writer; writerBuffer = writerBuffer; output = output } message =
    writerBuffer.Clear()
    writer.Reset()
    Json.serializeWriter writer message
    writer.Flush()

    outputBuffer.Clear()
    outputBuffer.Write(ReadOnlySpan utf8ContentLengthHeaderHead)
    outputBuffer.Write writerBuffer.WrittenCount
    outputBuffer.Write(ReadOnlySpan utf8HeaderEnd)
    output.Write outputBuffer.WrittenSpan
    output.Write writerBuffer.WrittenSpan

let writeJsonRpcResponse writer (response: _ JsonRpcResponse) = writeJson writer response
let writeJsonRpcNotification writer (notification: JsonRpcMessage<_,_,_>) = writeJson writer notification
