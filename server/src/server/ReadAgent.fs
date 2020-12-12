[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module LuaChecker.Server.ReadAgent
open LuaChecker.Server.Protocol
open LuaChecker.Server.Json
open LuaChecker.Server.Log
open LuaChecker.Text.Json
open System.Text.Json


let start agent =
    let rec loop agent =
        let r =
            try MessageReader.read Utf8Serializable.protocolValue<JsonRpcMessage<JsonElement, Methods, JsonElement>> agent.reader
            with :? JsonException -> Error MessageReader.ErrorKind.DeserializeFailure

        match r with
        | Error MessageReader.ErrorKind.EndOfSource -> ()
        | Error MessageReader.ErrorKind.RequireContentLengthHeader ->
            ifWarn { trace "Message was ignored." }
            loop agent

        | Error MessageReader.ErrorKind.DeserializeFailure ->
            ifWarn { trace "JSON RPC format is invalid." }
            loop agent

        | Error e -> ifError { Log.Format(agent.resources.LogMessages.MessageParseError, e) }

        | Ok { method = Defined Methods.exit } -> ifInfo { Log.Format agent.resources.LogMessages.ReceivedExitNotification }
        | Ok request ->
            ifDebug { Log.Format(agent.resources.LogMessages.MessageReceived, request) }
            agent.projectAgent.Post <| ProcessReceivedMessage request
            loop agent

    loop agent
    agent.projectAgent.Post QuitProjectAgent
