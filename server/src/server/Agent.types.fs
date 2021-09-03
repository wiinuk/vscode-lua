namespace LuaChecker.Server
open LuaChecker
open LuaChecker.Server.Protocol
open System
open System.Collections.Immutable
open System.Diagnostics
open System.Text.Json


type WriteAgent = {
    writer: MessageWriter.MessageWriter
}
type WriteAgentMessage =
    | WriteMessage of utf8Json: byte ReadOnlyMemory
    | QuitWriteAgent

type BackgroundAgent = {
    writeAgent: WriteAgentMessage MailboxProcessor
    semanticTokensDataBuffer: int ResizeArray
    watch: Stopwatch
}
[<Struct>]
type ResponseSemanticTokens = {
    requestId: int
    project: Project
    document: Document
    tree: TypedSyntaxes.Chunk
    rangeOrFull: Protocol.Range voption
    writeAgent: WriteAgentMessage MailboxProcessor
}
type BackgroundAgentMessage =
    | PublishDiagnostics of ProjectAgent * DocumentPath * version: int * Document voption * VarSubstitutions * LuaChecker.Diagnostic seq
    | EnumerateFiles of FileSystem * Uri * destination: ProjectAgentMessage MailboxProcessor
    | HoverHitTestAndResponse of requestId: int * agent: ProjectAgent * document: Document * tree: TypedSyntaxes.Chunk * position: Position
    | ResponseSemanticTokens of ResponseSemanticTokens
    | QuitBackgroundAgent

and ProjectAgent = {
    resourcePaths: string list
    project: Project
    root: Uri
    documents: Documents

    writeAgent: WriteAgentMessage MailboxProcessor
    /// `1 <= .Length`
    backgroundAgents: BackgroundAgentMessage MailboxProcessor ImmutableArray

    pendingCheckPaths: DocumentPath Set

    responseHandlers: Map<int, struct(ProjectAgent * Result<JsonElement, JsonRpcResponseError voption>) -> ProjectAgent>
    nextRequestId: int
    watch: Stopwatch
    random: Random
    nextDiagnosticsVersion: int
}

and ProjectAgentMessage =
    | ProcessReceivedMessage of JsonRpcMessage<JsonElement, Methods, JsonElement>
    | EnumerateFilesResponse of DocumentPath ImmutableArray
    | QuitProjectAgent

type ReadAgent = {
    reader: MessageReader.MessageReader
    projectAgent: ProjectAgentMessage MailboxProcessor
}
