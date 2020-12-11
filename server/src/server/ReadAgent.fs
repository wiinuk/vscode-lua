[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module LuaChecker.Server.ReadAgent
open LuaChecker.Server.Protocol
open LuaChecker.Server.Json
open LuaChecker.Server.Log
open LuaChecker.Text.Json
open System.Text.Json


let start state =
    let rec loop state =
        let r =
            try MessageReader.read Utf8Serializable.protocolValue<JsonRpcMessage<JsonElement, Methods, JsonElement>> state.reader
            with :? JsonException -> Error MessageReader.ErrorKind.DeserializeFailure

        match r with
        | Error MessageReader.ErrorKind.EndOfSource -> ()
        | Error MessageReader.ErrorKind.RequireContentLengthHeader ->
            ifWarn { trace "Message was ignored." }
            loop state

        | Error MessageReader.ErrorKind.DeserializeFailure ->
            ifWarn { trace "JSON RPC format is invalid." }
            loop state

        | Error e ->
            ifError { Log.Format(state.resources.LogMessages.MessageParseError, e) }

        | Ok { method = Defined Methods.exit } ->
            ifInfo { Log.Format state.resources.LogMessages.ReceivedExitNotification }

        | Ok request ->
            ifDebug { Log.Format(state.resources.LogMessages.MessageReceived, request) }
            state.projectAgent.Post <| ProcessReceivedMessage request
            loop state

    loop state
    state.writeAgent.Post QuitWriteAgent
    state.projectAgent.Post QuitProjectAgent
