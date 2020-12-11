namespace LuaChecker.Server
open LuaChecker
open LuaChecker.Server.Protocol
open System
open System.Diagnostics
open System.Text.Json


type WriteAgent = {
    resources: ServerResources.Resources
    writer: MessageWriter.MessageWriter
}
type WriteAgentMessage =
    | WriteMessage of utf8Json: byte ReadOnlyMemory
    | QuitWriteAgent

type ProjectAgent = {
    resources: ServerResources.Resources
    project: Project
    root: Uri
    documents: Documents

    writer: WriteAgentMessage MailboxProcessor

    pendingBackgroundCheckPaths: DocumentPath Set

    responseHandlers: Map<int, struct(ProjectAgent * Result<JsonElement, JsonRpcResponseError voption>) -> ProjectAgent>
    nextRequestId: int
    watch: Stopwatch
}

type ProjectAgentMessage =
    | ProcessReceivedMessage of JsonRpcMessage<JsonElement, Methods, JsonElement>
    | QuitProjectAgent

type ReadAgent = {
    reader: MessageReader.MessageReader
    resources: ServerResources.Resources
    writeAgent: WriteAgentMessage MailboxProcessor
    projectAgent: ProjectAgentMessage MailboxProcessor
}
