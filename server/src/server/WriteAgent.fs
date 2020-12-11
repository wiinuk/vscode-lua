[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module LuaChecker.Server.WriteAgent
open LuaChecker.Server.Log
open LuaChecker.Server.Protocol
open System.Text
open type WriteAgent


let create agent = new MailboxProcessor<_>(fun inbox ->
    let rec loop agent = async {
        match! inbox.Receive() with
        | QuitWriteAgent -> return ()
        | WriteMessage message ->
            ifDebug { Log.Format(agent.resources.LogMessages.RequestSending, Encoding.UTF8.GetString message.Span) }
            MessageWriter.writeRawMessage agent.writer message.Span

            return! loop agent
    }
    loop agent
)
