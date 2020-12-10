module LuaChecker.Server.Server
open Cysharp.Text
open LuaChecker
open LuaChecker.Checker
open LuaChecker.Primitives
open LuaChecker.Server.Log
open LuaChecker.Server.Protocol
open LuaChecker.Syntax
open LuaChecker.Text.Json
open LuaChecker.Text.Json.Parsing
open LuaChecker.TypedSyntaxes
open LuaChecker.TypeSystem
open System
open System.Collections.Concurrent
open System.Diagnostics
open System.IO
open System.Text.Json
open System.Threading
module S = LuaChecker.Syntaxes
type private Name = S.Name


type Document = {
    contents: string
    version: int
    lineMap: LineMap Lazy
}
module Document =
    let empty = { contents = ""; version = -1; lineMap = lazy LineMap.create "" }
    let create version contents = { contents = contents; version = version; lineMap = lazy LineMap.create contents }
    let positionToIndex { line = line; character = char } { lineMap = Lazy lineMap } =
        LineMap.lineStartPosition line lineMap + char

    let changeRange { start = start; ``end`` = end' } newVersion newText d =
        let start = positionToIndex start d
        let end' = positionToIndex end' d
        d.contents.Remove(start, end' - start).Insert(start, newText)
        |> create newVersion

type Documents = Map<DocumentPath, Document>
module Documents =
    let openedPaths documents = Map.toSeq documents |> Seq.map fst
    let tryFind path documents = Map.tryFind path documents
    let open' path text version documents =
        let document = Document.create version text
        Map.add path document documents

    let change path version changes documents =
        match version with
        | ValueNone ->
            ifDebug { trace "change ignored: %A" path }
            documents

        | ValueSome version ->

        match Map.tryFind path documents with
        | ValueNone -> documents
        | ValueSome document ->

        if version <= document.version then
            ifDebug { trace "received old version change" }
            documents
        else

        let document =
            changes
            |> Array.fold (fun document { text = text; range = range } ->
                match range with
                | Undefined -> Document.create version text
                | Defined range -> Document.changeRange range version text document
            ) document

        Map.add path document documents

    let close path documents = Map.remove path documents

type BackgroundChecker = {
    remainingPaths: ConcurrentDictionary<DocumentPath, HEmpty>
    mutable cancel: CancellationTokenSource
    mutable delay: TimeSpan
}
module BackgroundChecker =
    let create initialDelay = {
        remainingPaths = ConcurrentDictionary()
        cancel = new CancellationTokenSource()
        delay = initialDelay
    }

type MainThreadMessage =
    | Notification of Methods * task: unit Async
    | Response of id: int * task: byte ReadOnlyMemory Async * cancel: CancellationTokenSource
    | Request of task: Async<int * byte ReadOnlyMemory * (Result<JsonElement, JsonRpcResponseError option> -> unit)>
    | Quit

type Pipe = {
    messageQueue: MainThreadMessage BlockingCollection
    pendingRequests: ConcurrentDictionary<int, CancellationTokenSource>
}

type Server = {
    mutable resources: ServerResources.Resources
    mutable root: Uri
    mutable documents: Documents
    mutable project: Project
    input: MessageReader.MessageReader
    output: MessageWriter.MessageWriter

    backgroundChecker: BackgroundChecker
    pipe: Pipe
    requestIdToHandler: ConcurrentDictionary<int, Result<JsonElement, JsonRpcResponseError option> -> unit>
    mutable nextRequestId: int
    mutable isShutdownMessageReceived: bool
}
let serializeJsonRpcResponse id x =
    Json.serialize (JsonRpcMessage.successResponse id x)
    |> ReadOnlyMemory

let putResponseTask server id task =
    let task = async {
        let! r = task
        return serializeJsonRpcResponse id r
    }
    let cancel = new CancellationTokenSource()
    server.pipe.messageQueue.Add <| Response(id, task, cancel)
    server.pipe.pendingRequests.[id] <- cancel

let private options = ParserOptions.createFromParsers [
    JsonRegistrationParserFactory()
    FSharpRecordParserFactory()
    FSharpOptionParserFactory()
    FSharpValueOptionParserFactory()
    FSharpRecordOptionalFieldParserFactory()
    FSharpUnitParser()
]
let parse<'T> e = JsonElementParser.parse<'T> options e

let putRequestTask server task =
    let task = async {
        let! methods, ps, responseHandler = task
        let id = Interlocked.Increment &server.nextRequestId
        return id, Json.serialize (JsonRpcMessage.request id methods ps) |> ReadOnlyMemory, Result.map parse >> responseHandler
    }
    server.pipe.messageQueue.Add <| Request task

Utf16ValueStringBuilder.RegisterTryFormat(fun (value: _ ReadOnlyMemory) output written _ ->
    if value.Span.TryCopyTo output then
        written <- value.Length
        true
    else
        written <- 0
        false
)
Utf16ValueStringBuilder.RegisterTryFormat(fun (value: Utf16ValueStringBuilder) output written _ ->
    value.TryCopyTo(output, &written)
)

let writeNotification server message =
    ifDebug { Log.Format(server.resources.LogMessages.NotificationSending, message) }
    MessageWriter.writeJsonRpcNotification server.output message

let publishDiagnostics server filePath diagnostics =
    {
        uri = DocumentPath.toUri(filePath).ToString()
        diagnostics = diagnostics
    }
    |> ValueSome
    |> JsonRpcMessage.notification Methods.``textDocument/publishDiagnostics``
    |> writeNotification server

let marshalPosition (Position(line, char)) = {
    line = line
    character = char
}
let marshalSpanToRange lineMap { start = start; end' = end' } = {
    start = marshalPosition <| LineMap.findPosition start lineMap
    ``end`` = marshalPosition <| LineMap.findPosition end' lineMap
}
let marshalSeverity = function
    | Severity.Error -> DiagnosticSeverity.Error
    | Severity.Warning -> DiagnosticSeverity.Warning
    | Severity.Info -> DiagnosticSeverity.Information

let tagAndCount<'T>() =
    let tag = Reflection.FSharpValue.PreComputeUnionTagReader(typeof<'T>)
    (fun (x: 'T) -> tag x)

let parseErrorToTag = tagAndCount<ParseError>()
let unifyErrorToTag = tagAndCount<TypeSystem.UnifyError>()
let diagnosticKindToTag = tagAndCount<DiagnosticKind>()

let marshalDiagnosticKindToCode = function
    | DiagnosticKind.ParseError x -> 1 + parseErrorToTag x
    | DiagnosticKind.UnifyError x -> 1000 + unifyErrorToTag x
    | x -> 1100 + diagnosticKindToTag x - 2

let showPath x = DocumentPath.toUri(x).LocalPath
let showRelativePath server path =
    let root = Uri("file:///" + server.root.LocalPath).LocalPath
    Path.GetRelativePath(root, DocumentPath.toLocalPath path)

let (|Messages|) server = server.resources.DiagnosticMessages
type private P = Syntax.ParseError
type private K = LuaChecker.DiagnosticKind
module D = Documents

let showParseError (Messages m) = function
    | P.DisallowedLeadingNewLine -> m.DisallowedLeadingNewLine
    | P.RequireFieldSep -> m.RequireFieldSep
    | P.RequireAnyField -> m.RequireAnyField
    | P.RequireAnyStat -> m.RequireAnyStat
    | P.RequireAnyToken -> m.RequireAnyToken
    | P.RequireBinaryOp -> m.RequireBinaryOp
    | P.RequireFunctionCall -> m.RequireFunctionCall
    | P.RequireLiteral -> m.RequireLiteral
    | P.RequireName -> m.RequireName
    | P.RequireString -> m.RequireString
    | P.RequireToken t -> String.Format(m.RequireToken, t)
    | P.RequireUnaryOp -> m.RequireUnaryOp
    | P.RequireVar -> m.RequireVar
    | P.RequireAnyFieldKey -> m.RequireAnyFieldKey
    | P.RequireAnyTypeSign -> m.RequireAnyTypeSign

let showUnifyError (Messages m) = function
    | RequireField(x1, x2, x3) ->
        let x1 = x1 |> Seq.map (fun kv -> FieldKey.show kv.Key) |> String.concat ", "
        String.Format(m.RequireField, x1, FieldKey.show x2, Type.show x3)

    | TypeMismatch(x1, x2) ->
        String.Format(m.TypeMismatch, Type.show x1, Type.show x2)

    | UndefinedField(x1, x2) ->
        String.Format(m.UndefinedField, Type.show x1, FieldKey.show x2)

    | ConstraintAndTypeMismatch(x1, x2) ->
        String.Format(m.ConstraintAndTypeMismatch, Constraints.show x1.kind, Type.show x2)

    | ConstraintMismatch(x1, x2) ->
        String.Format(m.ConstraintMismatch, Constraints.show x1.kind, Constraints.show x2.kind)

    | KindMismatch(x1, x2) ->
        String.Format(m.KindMismatch, Kind.show x1, Kind.show x2)

    | TagSpaceConstraintMismatch(x1, x2, x3, x4) ->
        String.Format(m.TagSpaceConstraintMismatch, TagSpace.show x1, TagSpace.show x2, Type.show x3, TagElement.show x4)

let showSeverity (Messages m) = function
    | Severity.Error -> m.Error
    | Severity.Info -> m.Info
    | Severity.Warning -> m.Warning

let showFieldKey k =
    DocumentPrinter.fieldKey DocumentPrinter.Options.defaultOptions { kind = k; trivia = Span.empty }
    |> String.concat ""

let showSpan { start = s; end' = e } = sprintf "(%d, %d)" s e
let showTagName { Token.kind = kind } =
    match kind with
    | D.ClassTag _ -> "@class"
    | D.FeatureTag _ -> "@_Feature"
    | D.FieldTag _ -> "@field"
    | D.GenericTag _ -> "@generic"
    | D.GlobalTag _ -> "@global"
    | D.TypeTag _ -> "@type"
    | D.UnknownTag(Name n, _) -> "@" + n.kind

let showLocation server (Location(path, { start = s; end' = e })) =
    sprintf "%s(%d, %d)" (showRelativePath server path) s e

let showDeclSummary server name { scheme = t; location = l } =
    let location =
        match l with
        | None -> ""
        | Some l -> sprintf " -- %s" <| showLocation server l

    sprintf "%s: %s%s" name (Type.show t) location

let showTypeDefSummary server name { locations = ls } =
    let location =
        match List.tryHead ls with
        | None -> ""
        | Some l -> sprintf " -- %s" <| showLocation server l

    sprintf "%s: %s" name location

let showSystemType = function
    | SystemTypeCode.Nil -> "nil"
    | SystemTypeCode.Boolean -> "boolean"
    | SystemTypeCode.Number -> "number"
    | SystemTypeCode.String -> "string"
    | SystemTypeCode.Table -> "table"
    | SystemTypeCode.Thread -> "thread"

let showDeclKind (Messages m) = function
    | DeclarationKind.GlobalPackage -> m.GlobalPackage
    | DeclarationKind.GlobalRequire -> m.GlobalRequire
    | DeclarationKind.NoFeatures -> m.NoFeatures

let tryFindRange documents path span =
    match Documents.tryFind path documents with
    | ValueNone -> ValueNone
    | ValueSome d ->
        let lineMap = d.lineMap.Value
        ValueSome <| marshalSpanToRange lineMap span

let tryFindLocation documents path span =
    match tryFindRange documents path span with
    | ValueNone -> ValueNone
    | ValueSome range -> ValueSome { range = range; uri = DocumentPath.toUri(path).ToString() }

let rec showDiagnosticKind (Messages m & server) = function
    | K.ParseError x -> showParseError server x
    | K.UnifyError x -> showUnifyError server x
    | K.NameNotFound x -> String.Format(m.NameNotFound, x)
    | K.ReturnValueIgnored -> m.ReturnValueIgnored
    | K.IndirectGlobalRequireUse -> m.IndirectGlobalRequireUse
    | K.ModuleNotFound(x1, x2) -> String.Format(m.ModuleNotFound, x1, List.map showPath x2 |> String.concat "\n")
    | K.ExternalModuleError(x1, x2) -> String.Format(m.ExternalModuleError, showPath x1, showDiagnostic server x1 x2)
    | K.RecursiveModuleReference x1 -> String.Format(m.RecursiveModuleReference, showPath x1)
    | K.DuplicateFieldKey(k, otherFieldSpan) -> String.Format(m.DuplicateFieldKey, showFieldKey k, showSpan otherFieldSpan)
    | K.DuplicateTag otherTag -> String.Format(m.DuplicateTag, showTagName otherTag)
    | K.FieldParentTagNotFound -> m.FieldParentTagNotFound
    | K.GenericTagParentSyntaxNotFound -> m.GenericTagParentSyntaxNotFound
    | K.GlobalNameCollision(n, d1, d2, ds) ->
        String.Format(
            m.GlobalNameCollision,
            showDeclSummary server n d1,
            showDeclSummary server n d2,
            Seq.map (showDeclSummary server n >> (+) "\n") ds |> String.concat ""
        )
    | K.GlobalTypeCollision(n, d1, d2, ds) ->
        String.Format(
            m.GlobalTypeCollision,
            showTypeDefSummary server n d1,
            showTypeDefSummary server n d2,
            Seq.map (showTypeDefSummary server n >> (+) "\n") ds |> String.concat ""
        )
    | K.RedeclarationOfBasicType x -> String.Format(m.RedeclarationOfBasicType, showSystemType x)
    | K.RedeclarationOfSpecialGlobalVariable(name, oldKind, newKind) ->
        String.Format(
            m.RedeclarationOfSpecialGlobalVariable, name,
            showDeclKind server oldKind,
            showDeclKind server newKind
        )
    | K.RedeclarationOfTypeVariable(name, locs) ->
        String.Format(m.RedeclarationOfTypeVariable, name, Seq.map (showLocation server >> (+) "\n") locs |> String.concat "")

    | K.RequireMultiType -> m.RequireMultiType
    | K.TypeArityMismatch(expected, actual) -> String.Format(m.TypeArityMismatch, expected, actual)
    | K.TypeNameNotFound x -> String.Format(m.TypeNameNotFound, x)
    | K.TypeTagParentSyntaxNotFound -> m.TypeTagParentSyntaxNotFound

    | K.UndeterminedGlobalVariableEnvironment(modulePath, globals) ->
        let globals =
            globals
            |> Seq.map (fun kv ->
                let (NonEmptyList(d, _)) = kv.Value
                showDeclSummary server kv.Key d
            )
        String.Format(m.UndeterminedGlobalVariableEnvironment, showRelativePath server modulePath, globals)

    | K.UnexpectedMultiType -> m.UnexpectedMultiType
    | K.UnrecognizableGlobalPackageUse -> m.UnrecognizableGlobalPackageUse
    | K.UnrecognizedFeatureName x -> String.Format(m.UnrecognizedFeatureName, x)

and showDiagnostic server path (Diagnostic(span, severity, kind)) =
    let severity = showSeverity server severity
    let kind = showDiagnosticKind server kind
    match tryFindRange server.documents path span with
    | ValueNone -> sprintf "(%d, %d) %s: %s" (span.start + 1) (span.end' + 1) severity kind
    | ValueSome r ->
        sprintf "(%d,%d - %d,%d) %s: %s" (r.start.line + 1) (r.start.character + 1) (r.``end``.line + 1) (r.``end``.character + 1) severity kind

let marshalDiagnosticKindToTags = function
    | K.DuplicateFieldKey _
    | K.UnrecognizedFeatureName _
    | K.DuplicateTag _
    | K.FieldParentTagNotFound _
    | K.GenericTagParentSyntaxNotFound
    | K.TypeTagParentSyntaxNotFound -> Defined [|DiagnosticTag.Unnecessary|]
    | _ -> Undefined

let inline marshalCollisionInfoToRelatedInfo locations showSummary server (name, d1, d2, ds) =
    Defined [|
        for d in d1::d2::ds do
            for Location(path, span) in locations d do
                match tryFindLocation server.documents path span with
                | ValueNone -> ()
                | ValueSome location ->
                    let message = showSummary server name d
                    { location = location; message = message }
    |]

let marshalDiagnosticKindToRelatedInformation (Messages m as server) path document = function
    | K.ExternalModuleError(path, Diagnostic(span, _, kind)) ->
        match tryFindLocation server.documents path span with
        | ValueNone -> Undefined
        | ValueSome location ->
            Defined [|
                { location = location; message = showDiagnosticKind server kind }
            |]

    | K.DuplicateFieldKey(_, otherFieldSpan) ->
        Defined [|
            {
                location = {
                    uri = DocumentPath.toUri(path).ToString()
                    range = marshalSpanToRange document.lineMap.Value otherFieldSpan
                }
                message = m.OtherFieldLocation
            }
        |]
    | K.RedeclarationOfTypeVariable(_, oldTypeLocations) ->
        Defined [|
            for Location(path, span) in oldTypeLocations do
                match tryFindLocation server.documents path span with
                | ValueSome location -> { location = location; message = "" }
                | _ -> ()
        |]

    | K.GlobalNameCollision(name, d1, d2, ds) ->
        (name, d1, d2, ds)
        |> marshalCollisionInfoToRelatedInfo
            (fun d -> Option.toList d.location)
            showDeclSummary
            server

    | K.GlobalTypeCollision(name, t1, t2, ts) ->
        (name, t1, t2, ts)
        |> marshalCollisionInfoToRelatedInfo
            (fun t -> t.locations)
            showTypeDefSummary
            server

    | K.DuplicateTag otherTag ->
        match tryFindLocation server.documents path otherTag.trivia with
        | ValueSome location -> Defined [| { location = location; message = m.OtherTagLocation } |]
        | _ -> Undefined

    | _ -> Undefined

let marshalDocumentDiagnostics server path document diagnostics = async {
    let { lineMap = Lazy lineMap } = document

    return
        diagnostics
        |> Seq.map (fun (Diagnostic(span, severity, kind)) ->
            {
                source = ""
                range = marshalSpanToRange lineMap span
                severity = Defined <| marshalSeverity severity
                code = Defined <| marshalDiagnosticKindToCode kind
                message = showDiagnosticKind server kind
                tags = marshalDiagnosticKindToTags kind
                relatedInformation = marshalDiagnosticKindToRelatedInformation server path document kind
            }
        )
}

let checkOneFileAndResponse server path = async {
    match Map.tryFind path server.documents with
    | ValueNone -> ifError { trace "unopened file: %A" path }
    | ValueSome document ->

    let _, diagnostics, project, _ = Checker.parseAndCheckCached server.project path <| InMemory(document.contents, document.version)
    server.project <- project

    let! diagnostics = marshalDocumentDiagnostics server path document diagnostics
    publishDiagnostics server path <| Seq.toArray diagnostics
}

let runAllBackgroundCheck server = async {
    let bg = server.backgroundChecker
    do! Async.Sleep(int bg.delay.TotalMilliseconds)
    let keys = bg.remainingPaths.Keys
    let remainingCount = keys.Count
    if remainingCount <= 0 then () else
    let checkedCount = ref 0

    use! __ = Async.OnCancel <| fun _ ->
        ifDebug { trace "end bg check canceled %d/%d" !checkedCount remainingCount }

    ifDebug { trace "begin bg check %d/%d 0%%" !checkedCount remainingCount }
    for path in keys do
        let watch = Stopwatch.StartNew()
        do! checkOneFileAndResponse server path
        bg.remainingPaths.TryRemove path |> ignore
        incr checkedCount
        ifDebug {
            let percentage = !checkedCount * 100 / remainingCount
            trace "report bg check %d/%d %d%% %dms %A" !checkedCount remainingCount percentage watch.ElapsedMilliseconds path
        }
    ifDebug { trace "end bg check %d files" remainingCount }
}
let addBackgroundCheckList server path =
    let bg = server.backgroundChecker
    bg.remainingPaths.TryAdd(path, HEmpty) |> ignore
    bg.cancel.Cancel()
    bg.cancel.Dispose()
    bg.cancel <- new CancellationTokenSource()
    Async.Start(runAllBackgroundCheck server, bg.cancel.Token)

let checkAndResponse server path = async {
    match Map.tryFind path server.documents with
    | ValueNone -> ifError { trace "unopened file: %A" path }
    | ValueSome document ->

    let _, diagnostics, project, descendants = parseAndCheckCached server.project path (InMemory(document.contents, document.version))
    server.project <- project

    for d in descendants do
        addBackgroundCheckList server d

    let! diagnostics = marshalDocumentDiagnostics server path document diagnostics
    publishDiagnostics server path <| Seq.toArray diagnostics
}

module Async =
    let completed = async.Return()

type ServerCreateOptions = {
    resourcePaths: string list
    backgroundCheckDelay: TimeSpan
    fileSystem: FileSystem
    luaPath: string option
    platform: PlatformID option
    luaExeDirectory: string option
    caseSensitiveModuleResolve: bool
    globalModulePaths: string list
}
module ServerCreateOptions =
    let defaultOptions = {
        resourcePaths = []
        backgroundCheckDelay = TimeSpan.FromMilliseconds 2000.
        fileSystem = FileSystem.systemIO
        luaPath = None
        platform = None
        luaExeDirectory = None
        caseSensitiveModuleResolve = true
        globalModulePaths = [
            "standard.d.lua"
        ]
    }
let create withOptions (input, output, messageQueue) =
    let options = withOptions ServerCreateOptions.defaultOptions
    let packagePath = TopEnv.packagePath options.luaPath (defaultArg options.platform Environment.OSVersion.Platform) options.luaExeDirectory
    let rootUri = Uri "file:///"

    let project = Project.empty options.fileSystem (Checker.standardEnv packagePath) options.caseSensitiveModuleResolve
    let project =
        [ for path in options.globalModulePaths ->
            Path.Combine(Environment.CurrentDirectory, path) |> Path.GetFullPath |> Uri |> DocumentPath.ofUri rootUri
        ]
        |> Checker.addInitialGlobalModules project

    let pipe =
        let idToPendingRequest = ConcurrentDictionary()
        { pendingRequests = idToPendingRequest; messageQueue = messageQueue }
    {
        resources = ServerResources.loadFile options.resourcePaths
        root = rootUri
        documents = Map.empty
        project = project
        input = input
        output = output

        backgroundChecker = BackgroundChecker.create options.backgroundCheckDelay
        pipe = pipe
        requestIdToHandler = ConcurrentDictionary()
        nextRequestId = 1
        isShutdownMessageReceived = false
    }


let renderGenericAnnotationsInLua (b: Utf16ValueStringBuilder byref) (scope: _ inref) (state: _ byref) = function
    | [] -> ()
    | ps ->
        for p in ps do
            b.Append "---@generic "; TypeParameterExtensions.Append(&b, p, &scope, &state)
            b.Append '\n'

let reset (x: 'T byref when 'T :> IResettableBufferWriter<_> and 'T : struct) = x.Reset()

let renderInstantiatedVar (Messages M) (scope: _ inref) (state: _ byref) (varSymbol: Utf16ValueStringBuilder inref) (genScheme: Scheme, pts) =
    use mutable b = ZString.CreateStringBuilder()

    let struct(ps, t) = Scheme.takeHeadParameters [] genScheme
    b.Append "```lua\n"
    renderGenericAnnotationsInLua &b &scope &state ps
    b.Append(varSymbol.AsSpan()); b.Append ": "; TypeExtensions.Append(&b, t.kind, &scope, &state); b.Append '\n'
    b.Append '\n'
    b.Append "-- "; b.Append M.GenericTypeParameters; b.Append '\n'

    let scope = TypePrintScope.empty
    let mutable state = TypePrintState.create TypeWriteOptions.Default

    use mutable b1 = ZString.CreateStringBuilder()
    use mutable b2 = ZString.CreateStringBuilder()
    match pts with
    | [] -> ()
    | _ ->
        for struct(TypeParameterId(id, _), { Token.kind = t }) in pts do
            b1.Append id
            TypeExtensions.Append(&b2, t, &scope, &state)

            b.Append "-- "; b.AppendFormat(M.GenericTypeSubstitute, b1, b2); b.Append '\n'
            reset &b1
            reset &b2

    b.Append "```"
    b.ToString()

let renderVarCore server (varSymbol: _ inref) t info =
    let scope = TypePrintScope.empty
    let mutable state = TypePrintState.create TypeWriteOptions.Default

    match info with
    | ValueSome { schemeInstantiation = ValueSome x } -> renderInstantiatedVar server &scope &state &varSymbol x
    | _ ->

    let struct(ps, t) = Scheme.takeHeadParameters [] t
    use mutable b = ZString.CreateStringBuilder()
    b.Append "```lua\n"
    renderGenericAnnotationsInLua &b &scope &state ps
    b.Append(varSymbol.AsSpan()); b.Append ": "; b.Append(t.kind, &scope, &state)
    b.Append "\n```"
    b.ToString()

let renderVar server (Var(Name.Name { kind = n }, t, info)) =
    use mutable name = ZString.CreateStringBuilder()
    name.Append n
    renderVarCore server &name t info

let renderReserved server (ReservedVar(_, k, t, info)) =
    use mutable symbolName = ZString.CreateStringBuilder()
    symbolName.Append '('
    for x in Printer.showKind Printer.PrintConfig.defaultConfig k do
        symbolName.Append x
    symbolName.Append ')'

    renderVarCore server &symbolName t info

let renderModulePath server modulePath =
    use mutable b = ZString.CreateStringBuilder()
    let moduleUri = DocumentPath.toUri modulePath
    let relativePath = showRelativePath server modulePath

    // [libraries/lib1.lua](file:///C:/workspace/libraries/lib1.lua)
    b.Append '['; b.Append relativePath; b.Append "]("; b.Append moduleUri; b.Append ")"

    b.ToString()

let renderSimpleType (b: Utf16ValueStringBuilder byref) t =
    let scope = TypePrintScope.empty
    let mutable state = TypePrintState.create TypeWriteOptions.Default

    let struct(ps, t) = Scheme.takeHeadParameters [] t
    b.Append "```lua\n"
    renderGenericAnnotationsInLua &b &scope &state ps
    b.Append(t.kind, &scope, &state)
    b.Append "\n```"

let renderLiteral server t info =
    match info with
    | ValueSome { externalModulePath = ValueSome modulePath } -> renderModulePath server modulePath
    | _ ->

    use mutable b = ZString.CreateStringBuilder()
    renderSimpleType &b t
    b.ToString()

let renderTypeTag t =
    use mutable b = ZString.CreateStringBuilder()
    renderSimpleType &b t
    b.ToString()

let prettyTokenInfo = {
    var = fun struct(s, x, _) -> renderVar s x
    reserved = fun struct(s, x, _) -> renderReserved s x
    literal = fun struct(s, _, t, _, i) -> renderLiteral s t i
    typeTag = fun struct(_, _, t, _) -> renderTypeTag t
}

module Interfaces =
    let initialized server =
        putRequestTask server <| async {
            let options = {|
                watchers = [|
                    {| globPattern = "**/*.lua" |}
                |]
            |}
            let ps = {|
                registrations = [|
                    {|
                        id = Guid.NewGuid()
                        method = Methods.``workspace/didChangeWatchedFiles``
                        registerOptions = options
                    |}
                |]
            |}
            let responseHandler = function Error e -> ifWarn { Log.Format(server.resources.LogMessages.ErrorResponseReceived, e) } | Ok() -> ()
            return  Methods.``client/registerCapability``, ValueSome ps, responseHandler
        }
        Async.completed

    let initialize server id { rootUri = rootUri } = putResponseTask server id <| async {
        match rootUri with
        | ValueSome root -> server.root <- root
        | _ -> ()

        return {
            capabilities = {
                hoverProvider = true
                textDocumentSync = {
                    openClose = true
                    save = Defined { includeText = false }
                    change = TextDocumentSyncKind.Incremental
                }
            }
        }
    }
    let shutdown server id () = putResponseTask server id <| async {
        server.isShutdownMessageReceived <- true
    }

    let didChangeConfiguration _ (p: struct {| settings: JsonElement |}) =
        ifInfo { trace "config updated: %s" <| p.settings.GetRawText() }
        Async.completed

    let didOpenTextDocument server { DidOpenTextDocumentParams.textDocument = d } = async {
        let path = DocumentPath.ofUri server.root d.uri
        server.documents <- Documents.open' path d.text d.version server.documents

        do! checkAndResponse server path
    }
    let didChangeTextDocument server { textDocument = d; contentChanges = contentChanges } = async {
        let path = DocumentPath.ofUri server.root d.uri
        let documents = Documents.change path d.version contentChanges server.documents
        server.documents <- documents

        addBackgroundCheckList server path
    }
    let didCloseTextDocument server (p: struct {| textDocument: TextDocumentIdentifier |}) = async {
        let path = DocumentPath.ofUri server.root p.textDocument.uri
        server.documents <- Documents.close path server.documents
        publishDiagnostics server path [||]
    }
    let didSaveTextDocument server { DidSaveTextDocumentParams.textDocument = textDocument } = async {
        let savedFile = DocumentPath.ofUri server.root textDocument.uri

        let files = [|
            for path in Documents.openedPaths server.documents do
                if Checker.isAncestor savedFile path server.project then
                    path
        |]

        for file in files do
            addBackgroundCheckList server file
    }
    let didChangeWatchedFiles server { changes = changes } = async {
        for change in changes do
            let path = DocumentPath.ofUri server.root change.uri
            ifDebug { trace "changed %A %A" path change.``type`` }

            let (DocumentPath p) = path
            if p.EndsWith ".lua" then
                let struct(project, descendants) =
                    match change.``type`` with
                    | FileChangeType.Created -> Checker.addOrUpdateSourceFile path server.project
                    | FileChangeType.Changed -> Checker.addOrUpdateSourceFile path server.project
                    | FileChangeType.Deleted -> Checker.removeSourceFile path server.project
                    | t ->
                        ifWarn { trace "unknown FileChangeType: %A" t }
                        server.project, []
                server.project <- project

                addBackgroundCheckList server path
                for path in descendants do
                    addBackgroundCheckList server path
    }
    let hover server id { HoverParams.textDocument = textDocument; position = position } = putResponseTask server id <| async {
        let path = DocumentPath.ofUri server.root textDocument.uri
        match Documents.tryFind path server.documents with
        | ValueNone -> return ValueNone
        | ValueSome document ->

        let index = Document.positionToIndex position document
        let result, project = Checker.hitTest server.project prettyTokenInfo server path index
        server.project <- project

        match result with
        | ValueNone -> return ValueNone
        | ValueSome markdown ->

        let markdown = { kind = MarkupKind.markdown; value = markdown }
        return ValueSome { contents = markdown; range = Undefined }
    }
