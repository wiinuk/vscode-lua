[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module LuaChecker.Server.WriteAgent
open LuaChecker.Server.Log
open LuaChecker.Server.Protocol
open System
open System.Text
open type WriteAgent


let sendResponse (agent: _ MailboxProcessor) id result =
    let jsonBytes =
        match result with
        | Ok result -> JsonRpcMessage.successResponse id result
        | Error e -> JsonRpcMessage.errorResponse id e
        |> Json.serialize
        |> ReadOnlyMemory

    agent.Post <| WriteMessage jsonBytes

let create agent = new MailboxProcessor<_>(fun inbox ->
    let rec loop agent = async {
        match! inbox.Receive() with
        | QuitWriteAgent -> return ()
        | WriteMessage message ->
            ifDebug { Log.Format(agent.resources.LogMessages.MessageSending, Encoding.UTF8.GetString message.Span) }
            MessageWriter.writeRawMessage agent.writer message.Span

            return! loop agent
    }
    loop agent
)
