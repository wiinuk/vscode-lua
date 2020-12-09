namespace LuaChecker.Server.Protocol
open System
open System.Text.Json
open LuaChecker.Text.Json


type Methods =
    | Unknown = 0uy
    | ``$/cancelRequest`` = 1uy
    | ``$/progress`` = 2uy
    | ``client/registerCapability`` = 3uy
    | ``client/unregisterCapability`` = 4uy
    | ``codeLens/resolve`` = 5uy
    | ``completionItem/resolve`` = 6uy
    | ``documentLink/resolve`` = 7uy
    | ``exit`` = 8uy
    | ``initialize`` = 9uy
    | ``initialized`` = 10uy
    | ``shutdown`` = 11uy
    | ``telemetry/event`` = 12uy
    | ``textDocument/codeAction`` = 13uy
    | ``textDocument/codeLens`` = 14uy
    | ``textDocument/colorPresentation`` = 15uy
    | ``textDocument/completion`` = 16uy
    | ``textDocument/declaration`` = 17uy
    | ``textDocument/definition`` = 18uy
    | ``textDocument/didChange`` = 19uy
    | ``textDocument/didClose`` = 20uy
    | ``textDocument/didOpen`` = 21uy
    | ``textDocument/didSave`` = 22uy
    | ``textDocument/documentColor`` = 23uy
    | ``textDocument/documentHighlight`` = 24uy
    | ``textDocument/documentLink`` = 25uy
    | ``textDocument/documentSymbol`` = 26uy
    | ``textDocument/foldingRange`` = 27uy
    | ``textDocument/formatting`` = 28uy
    | ``textDocument/hover`` = 29uy
    | ``textDocument/implementation`` = 30uy
    | ``textDocument/onTypeFormatting`` = 31uy
    | ``textDocument/prepareRename`` = 32uy
    | ``textDocument/publishDiagnostics`` = 33uy
    | ``textDocument/rangeFormatting`` = 34uy
    | ``textDocument/references`` = 35uy
    | ``textDocument/rename`` = 36uy
    | ``textDocument/selectionRange`` = 37uy
    | ``textDocument/signatureHelp`` = 38uy
    | ``textDocument/typeDefinition`` = 39uy
    | ``textDocument/willSave`` = 40uy
    | ``textDocument/willSaveWaitUntil`` = 41uy
    | ``window/logMessage`` = 42uy
    | ``window/showMessage`` = 43uy
    | ``window/showMessageRequest`` = 44uy
    | ``window/workDoneProgress/cancel`` = 45uy
    | ``window/workDoneProgress/create`` = 46uy
    | ``workspace/applyEdit`` = 47uy
    | ``workspace/configuration`` = 48uy
    | ``workspace/didChangeConfiguration`` = 49uy
    | ``workspace/didChangeWatchedFiles`` = 50uy
    | ``workspace/didChangeWorkspaceFolders`` = 51uy
    | ``workspace/executeCommand`` = 52uy
    | ``workspace/symbol`` = 53uy
    | ``workspace/workspaceFolders`` = 54uy

type JsonRpcVersion =
    | ``2.0`` = 2uy

type JsonRpcResponse<'T> = {
    jsonrpc: JsonRpcVersion
    id: int
    result: 'T
}
module JsonRpcErrorCodes =

    // JSON RPC
    let ParseError = -32700
    let InvalidRequest = -32600
    let MethodNotFound = -32601
    let InvalidParams = -32602
    let InternalError = -32603
    let serverErrorStart = -32099
    let serverErrorEnd = -32000
    let ServerNotInitialized = -32002
    let UnknownErrorCode = -32001

    // LSP
    let RequestCancelled = -32800
    let ContentModified = -32801

type JsonRpcResponseError = {
    code: int
    message: string
    data: JsonElement OptionalField
}
type JsonRpcMessage<'T,'M,'R> = {
    jsonrpc: JsonRpcVersion
    id: int OptionalField
    method: 'M OptionalField
    ``params``: 'T OptionalField
    result: 'R OptionalField
    error: JsonRpcResponseError OptionalField
}
module JsonRpcMessage =
    let notification method ``params`` = {
        jsonrpc = JsonRpcVersion.``2.0``
        id = Undefined
        method = Defined method
        ``params`` = ``params``
        result = Undefined
        error = Undefined
    }
    let request id method  ``params`` = {
        jsonrpc = JsonRpcVersion.``2.0``
        id = Defined id
        method = Defined method
        ``params`` = ``params``
        result = Undefined
        error = Undefined
    }
    let successResponse id result = {
        jsonrpc = JsonRpcVersion.``2.0``
        id = Defined id
        result = Defined result
        method = Undefined
        ``params`` = Undefined
        error = Undefined
    }
    let errorResponse id error = {
        jsonrpc = JsonRpcVersion.``2.0``
        id = Defined id
        error = error
        method = Undefined
        ``params`` = Undefined
        result = Undefined
    }

type boolean = bool

type TextDocumentItem = {
    uri: Uri
    version: int
    text: string
}
type TextDocumentSyncKind =
    | None = 0
    | Full = 1
    | Incremental = 2

[<Struct>]
type Position = {
    /// 0..
    line: int
    /// 0..
    character: int
}

[<Struct>]
type Range = {
    start: Position
    ``end``: Position
}
type Location = {
    uri: string
    range: Range
}

type DiagnosticSeverity =
    | Error = 1uy
    | Warning = 2uy
    | Information = 3uy
    | Hint = 4uy

type DiagnosticTag =
    | Unnecessary = 1uy
    | Deprecated = 2uy

type DiagnosticRelatedInformation = {
    location: Location
    message: string
}
type Diagnostic = {
    range: Range
    severity: DiagnosticSeverity OptionalField
    code: int OptionalField
    /// maybe null
    source: string
    message: string
    tags: DiagnosticTag array OptionalField
    relatedInformation: DiagnosticRelatedInformation array OptionalField
}

[<Struct>]
type PublishDiagnosticsParams = {
    uri: string
    diagnostics: Diagnostic array
}
[<Struct>]
type VersionedTextDocumentIdentifier = {
    uri: Uri
    version: int voption
}
type TextDocumentContentChangeEvent = {
    range: Range OptionalField
    text: string
}
[<Struct>]
type TextDocumentIdentifier = {
    uri: Uri
}

/// `string | number`
type ProgressToken = JsonElement

[<JsonElementParser(typeof<EnumToStringParser<MarkupKind>>)>]
type MarkupKind =
    | plaintext = 0uy
    | markdown = 1uy

[<Struct>]
type MarkupContent = {
    kind: MarkupKind
    value: string
}
type Hover = {
    contents: MarkupContent
    range: Range OptionalField
}
type FileChangeType =
    | Created = 1uy
    | Changed = 2uy
    | Deleted = 3uy

[<Struct>]
type FileEvent = {
    uri: Uri
    ``type``: FileChangeType
}
[<Struct>]
type InitializeParams = {
    rootUri: Uri voption
}
[<Struct>]
type DidOpenTextDocumentParams = {
    textDocument: TextDocumentItem
}
[<Struct>]
type DidSaveTextDocumentParams = {
    textDocument: TextDocumentIdentifier
}
[<Struct>]
type SaveOptions = {
    includeText: bool
}
type TextDocumentSyncOptions = {
    openClose: bool
    save: SaveOptions OptionalField
    change: TextDocumentSyncKind
}
[<Struct>]
type ServerCapabilities = {
    hoverProvider: bool
    textDocumentSync: TextDocumentSyncOptions
}
[<Struct>]
type InitializeResult = {
    capabilities: ServerCapabilities
}
type DidChangeTextDocumentParams = {
    textDocument: VersionedTextDocumentIdentifier
    contentChanges: TextDocumentContentChangeEvent array
}
[<Struct>]
type DidChangeWatchedFilesParams = {
    changes: FileEvent array
}
[<Struct>]
type HoverParams = {
    textDocument: TextDocumentIdentifier
    position: Position
}
