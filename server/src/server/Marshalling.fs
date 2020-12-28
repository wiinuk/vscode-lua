module LuaChecker.Server.Marshalling
#nowarn "0069"
open Cysharp.Text
open LuaChecker
open LuaChecker.Server.Protocol
open LuaChecker.Syntax
open LuaChecker.Primitives
open LuaChecker.Text.Json
open LuaChecker.TypeSystem
open LuaChecker.TypedSyntaxes
open System
open System.Diagnostics.CodeAnalysis
module S = LuaChecker.Syntaxes
module D = LuaChecker.Syntax.Documents
type private L = LuaChecker.LeafFlags


type MarshallingContext = {
    root: Uri
    resources: ServerResources.Resources
    documents: Documents
}

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

let marshalPosition (Position(line, char)) = {
    line = line
    character = char
}
let positionToIndex lineMap position =
    LineMap.lineStartPosition position.line lineMap + position.character

let rangeToSpan lineMap range = {
    start = positionToIndex lineMap range.start
    end' = positionToIndex lineMap range.``end``
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

let showPath x =
    match DocumentPath.toPathOrNone x with
    | ValueSome x -> x
    | _ -> DocumentPath.toUriString x

let showRelativePath context path =
    let pathInRoot = DocumentPath.toUri path |> context.root.MakeRelativeUri
    if pathInRoot.IsAbsoluteUri
    then DocumentPath.ofUri pathInRoot |> showPath
    else pathInRoot.ToString()

let (|Messages|) context = context.resources.DiagnosticMessages
type private P = Syntax.ParseError
type private K = LuaChecker.DiagnosticKind
module D = Documents

let showParseError (Messages m) = function
    | P.DisallowedLeadingNewLine -> m.DisallowedLeadingNewLine
    | P.RequireFieldSep -> m.RequireFieldSep
    | P.RequireAnyField -> m.RequireAnyField
    | P.RequireAnyStat -> m.RequireAnyStat
    | P.RequireBinaryOp -> m.RequireBinaryOp
    | P.RequireLiteral -> m.RequireLiteral
    | P.RequireName -> m.RequireName
    | P.RequireString -> m.RequireString
    | P.RequireToken t -> String.Format(m.RequireToken, Printer.showKind Printer.PrintConfig.defaultConfig t |> String.concat "")
    | P.RequireUnaryOp -> m.RequireUnaryOp
    | P.RequireVar -> m.RequireVar
    | P.RequireAnyFieldKey -> m.RequireAnyFieldKey
    | P.RequireAnyTypeSign -> m.RequireAnyTypeSign
    | P.RequireAssignStatOrFunctionCall -> m.RequireAssignStatOrFunctionCall
    | P.RequireEndOfSource -> m.RequireEndOfSource
    | P.RequireNameOrDot3 -> m.RequireNameOrDot3
    | P.RequireNameOrLBracket -> m.RequireNameOrLBracket

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
    DocumentPrinter.fieldKey DocumentPrinter.Options.defaultOptions (D.Annotated({ kind = k; trivia = Span.empty }, HEmpty))
    |> String.concat ""

let showSpan { start = s; end' = e } = sprintf "(%d, %d)" s e

let showLocation context (Location(path, { start = s; end' = e })) =
    sprintf "%s(%d, %d)" (showRelativePath context path) s e

let showDeclSummary context name { scheme = t; location = l } =
    let location =
        match l with
        | None -> ""
        | Some l -> sprintf " -- %s" <| showLocation context l

    sprintf "%s: %s%s" name (Type.show t) location

let showTypeDefSummary context name { locations = ls } =
    let location =
        match List.tryHead ls with
        | None -> ""
        | Some l -> sprintf " -- %s" <| showLocation context l

    sprintf "%s: %s" name location

let showSystemType = function
    | SystemTypeCode.Nil -> "nil"
    | SystemTypeCode.Boolean -> "boolean"
    | SystemTypeCode.Number -> "number"
    | SystemTypeCode.String -> "string"
    | SystemTypeCode.Table -> "table"
    | SystemTypeCode.Thread -> "thread"

let showDeclFeatures (Messages m) = function
    | DeclarationFeatures.GlobalPackage -> m.GlobalPackage
    | DeclarationFeatures.GlobalRequire -> m.GlobalRequire
    | DeclarationFeatures.NoFeatures -> m.NoFeatures

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

let rec showDiagnosticKind (Messages m & context) = function
    | K.ParseError x -> showParseError context x
    | K.UnifyError x -> showUnifyError context x
    | K.NameNotFound x -> String.Format(m.NameNotFound, x)
    | K.ReturnValueIgnored -> m.ReturnValueIgnored
    | K.IndirectGlobalRequireUse -> m.IndirectGlobalRequireUse
    | K.ModuleNotFound(x1, x2) -> String.Format(m.ModuleNotFound, x1, List.map showPath x2 |> String.concat "\n")
    | K.ExternalModuleError(x1, x2) -> String.Format(m.ExternalModuleError, showPath x1, showDiagnostic context x1 x2)
    | K.RecursiveModuleReference x1 -> String.Format(m.RecursiveModuleReference, showPath x1)
    | K.DuplicateFieldKey(k, otherFieldSpan) -> String.Format(m.DuplicateFieldKey, showFieldKey k, showSpan otherFieldSpan)
    | K.DuplicateTag(otherTagName, otherTagSpan) -> String.Format(m.DuplicateTag, otherTagName, otherTagSpan)
    | K.FieldParentTagNotFound -> m.FieldParentTagNotFound
    | K.GenericTagParentSyntaxNotFound -> m.GenericTagParentSyntaxNotFound
    | K.GlobalNameCollision(n, d1, d2, ds) ->
        String.Format(
            m.GlobalNameCollision,
            showDeclSummary context n d1,
            showDeclSummary context n d2,
            Seq.map (showDeclSummary context n >> (+) "\n") ds |> String.concat ""
        )
    | K.GlobalTypeCollision(n, d1, d2, ds) ->
        String.Format(
            m.GlobalTypeCollision,
            showTypeDefSummary context n d1,
            showTypeDefSummary context n d2,
            Seq.map (showTypeDefSummary context n >> (+) "\n") ds |> String.concat ""
        )
    | K.RedeclarationOfBasicType x -> String.Format(m.RedeclarationOfBasicType, showSystemType x)
    | K.RedeclarationOfSpecialGlobalVariable(name, oldFeatures, newFeatures) ->
        String.Format(
            m.RedeclarationOfSpecialGlobalVariable, name,
            showDeclFeatures context oldFeatures,
            showDeclFeatures context newFeatures
        )
    | K.RedeclarationOfTypeVariable(name, locs) ->
        String.Format(m.RedeclarationOfTypeVariable, name, Seq.map (showLocation context >> (+) "\n") locs |> String.concat "")

    | K.RequireMultiType -> m.RequireMultiType
    | K.TypeArityMismatch(expected, actual) -> String.Format(m.TypeArityMismatch, expected, actual)
    | K.TypeNameNotFound x -> String.Format(m.TypeNameNotFound, x)
    | K.TypeTagParentSyntaxNotFound -> m.TypeTagParentSyntaxNotFound

    | K.UndeterminedGlobalVariableEnvironment(modulePath, globals) ->
        let globals =
            globals
            |> Seq.map (fun kv ->
                let (NonEmptyList(d, _)) = kv.Value
                showDeclSummary context kv.Key d
            )
        String.Format(m.UndeterminedGlobalVariableEnvironment, showRelativePath context modulePath, globals)

    | K.UnexpectedMultiType -> m.UnexpectedMultiType
    | K.UnrecognizableGlobalPackageUse -> m.UnrecognizableGlobalPackageUse
    | K.UnrecognizedFeatureName x -> String.Format(m.UnrecognizedFeatureName, x)

and showDiagnostic context path (Diagnostic(span, severity, kind)) =
    let severity = showSeverity context severity
    let kind = showDiagnosticKind context kind
    match tryFindRange context.documents path span with
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

[<SuppressMessage("PublicUnusedMemberAnalyzer.fsx", "AA0001:MemberUnused")>]
let inline marshalCollisionInfoToRelatedInfo locations showSummary context (name, d1, d2, ds) =
    Defined [|
        for d in d1::d2::ds do
            for Location(path, span) in locations d do
                match tryFindLocation context.documents path span with
                | ValueNone -> ()
                | ValueSome location ->
                    let message = showSummary context name d
                    { location = location; message = message }
    |]

let marshalDiagnosticKindToRelatedInformation (Messages m as context) path document = function
    | K.ExternalModuleError(path, Diagnostic(span, _, kind)) ->
        match tryFindLocation context.documents path span with
        | ValueNone -> Undefined
        | ValueSome location ->
            Defined [|
                { location = location; message = showDiagnosticKind context kind }
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
                match tryFindLocation context.documents path span with
                | ValueSome location -> { location = location; message = "" }
                | _ -> ()
        |]

    | K.GlobalNameCollision(name, d1, d2, ds) ->
        (name, d1, d2, ds)
        |> marshalCollisionInfoToRelatedInfo
            (fun d -> Option.toList d.location)
            showDeclSummary
            context

    | K.GlobalTypeCollision(name, t1, t2, ts) ->
        (name, t1, t2, ts)
        |> marshalCollisionInfoToRelatedInfo
            (fun t -> t.locations)
            showTypeDefSummary
            context

    | K.DuplicateTag(_, otherTagSpan) ->
        match tryFindLocation context.documents path otherTagSpan with
        | ValueSome location -> Defined [| { location = location; message = m.OtherTagLocation } |]
        | _ -> Undefined

    | _ -> Undefined

let marshalDocumentDiagnostics context path document diagnostics =
    let { lineMap = Lazy lineMap } = document

    diagnostics
    |> Seq.map (fun (Diagnostic(span, severity, kind)) ->
        {
            source = ""
            range = marshalSpanToRange lineMap span
            severity = Defined <| marshalSeverity severity
            code = Defined <| marshalDiagnosticKindToCode kind
            message = showDiagnosticKind context kind
            tags = marshalDiagnosticKindToTags kind
            relatedInformation = marshalDiagnosticKindToRelatedInformation context path document kind
        }
    )

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

let renderVarCore context (varSymbol: _ inref) t info =
    let scope = TypePrintScope.empty
    let mutable state = TypePrintState.create TypeWriteOptions.Default

    match info with
    | ValueSome { schemeInstantiation = ValueSome x } -> renderInstantiatedVar context &scope &state &varSymbol x
    | _ ->

    let struct(ps, t) = Scheme.takeHeadParameters [] t
    use mutable b = ZString.CreateStringBuilder()
    b.Append "```lua\n"
    renderGenericAnnotationsInLua &b &scope &state ps
    b.Append(varSymbol.AsSpan()); b.Append ": "; b.Append(t.kind, &scope, &state)
    b.Append "\n```"
    b.ToString()

let renderVar context (Var(s, k, _, Name { kind = n }, t, info)) =
    use mutable name = ZString.CreateStringBuilder()
    match s, k with
    | IdentifierScope.Global, IdentifierKind.Variable -> name.Append "---@global "
    | IdentifierScope.Local, (IdentifierKind.Variable | IdentifierKind.Parameter) -> name.Append "local "
    | _, IdentifierKind.Field -> name.Append "."
    | _, IdentifierKind.Method -> name.Append ":"
    | _ -> ()
    name.Append n
    renderVarCore context &name t info

let renderReserved context (ReservedVar(_, k, t, info)) =
    use mutable symbolName = ZString.CreateStringBuilder()
    symbolName.Append '('
    for x in Printer.showKind Printer.PrintConfig.defaultConfig k do
        symbolName.Append x
    symbolName.Append ')'

    renderVarCore context &symbolName t info

let renderModulePath context modulePath =
    use mutable b = ZString.CreateStringBuilder()
    let moduleUri = DocumentPath.toUri modulePath
    let relativePath = showRelativePath context modulePath

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

let renderLiteral context t info =
    match info with
    | ValueSome { externalModulePath = ValueSome modulePath } -> renderModulePath context modulePath
    | _ ->

    use mutable b = ZString.CreateStringBuilder()
    renderSimpleType &b t
    b.ToString()

[<Struct>]
type PrettyTokenVisitor = {
    marshallingContext: MarshallingContext
    mutable renderedText: string
}
with
    interface ITypedSyntaxVisitor with
        member v.Var(x, _) = v.renderedText <- renderVar v.marshallingContext x
        member v.Reserved(x, _) = v.renderedText <- renderReserved v.marshallingContext x
        member v.Literal(_, t, _, i) = v.renderedText <- renderLiteral v.marshallingContext t i

        // TODO:
        member _.DocumentFieldIdentifier _ = ()
        member _.DocumentFieldSeparator _ = ()
        member _.DocumentFieldVisibility _ = ()
        member _.DocumentIdentifier _ = ()
        member _.DocumentReserved _ = ()

(*
#r "nuget: HtmlAgilityPack"
#r "nuget: FSharp.Compiler.Service"
open HtmlAgilityPack
open System.Net
open FSharp.Compiler.SourceCodeServices.Keywords
open type System.Text.RegularExpressions.Regex

let uri = "https://microsoft.github.io/language-server-protocol/specifications/specification-current/"

let html = new HtmlDocument()
html.LoadHtml(use wc = new WebClient() in wc.DownloadString uri)
let enumValues enumName = [
    for code in html.DocumentNode.SelectNodes "//code" do
        let code = code.InnerText
        if IsMatch(code, @$"\benum\s+{enumName}\b") then
            let enumMembers = Match(code, @$"\benum\s+{enumName}\s*\{{([^}}]*?)\}}")
            for m in Matches(enumMembers.Groups.[1].Value, @"\w+\s*=\s*'([^']*)?'") do
                m.Groups.[1].Value
]
let name n = if DoesIdentifierNeedQuotation n then $"``{n}``" else n

printfn "type KnownSemanticTokenTypes ="
let ts = enumValues "SemanticTokenTypes"
for i, n in Seq.indexed ts do
    printfn $"    | {name n} = {i}"
printfn $"    | KnownMax = {List.length ts - 1}"
printfn ""
let ms = enumValues "SemanticTokenModifiers"
printfn "[<Flags>]"
printfn "type KnownSemanticTokenModifiers ="
printfn "    | Empty = 0"
for i, n in List.indexed ms do
    printfn $"    | {name n} = {pown 2 i}"
printfn $"    | KnownMaxBitCount = {List.length ms - 1}"
*)
type KnownSemanticTokenTypes =
    | ``namespace`` = 0
    | ``type`` = 1
    | ``class`` = 2
    | enum = 3
    | ``interface`` = 4
    | ``struct`` = 5
    | typeParameter = 6
    | parameter = 7
    | variable = 8
    | property = 9
    | enumMember = 10
    | event = 11
    | ``function`` = 12
    | method = 13
    | macro = 14
    | keyword = 15
    | modifier = 16
    | comment = 17
    | string = 18
    | number = 19
    | regexp = 20
    | operator = 21
    | KnownMax = 21

[<Flags>]
type KnownSemanticTokenModifiers =
    | Empty = 0
    | declaration = 1
    | definition = 2
    | readonly = 4
    | ``static`` = 8
    | deprecated = 16
    | ``abstract`` = 32
    | async = 64
    | modification = 128
    | documentation = 256
    | defaultLibrary = 512
    | KnownMaxBitCount = 9

let semanticTokenTypeLegend = [
    for n in Enum.GetNames typeof<KnownSemanticTokenTypes> do
        if Char.IsLower n.[0] then
            n
]
let semanticTokenModifiersLegend = [
    for n in Enum.GetNames typeof<KnownSemanticTokenModifiers> do
        if Char.IsLower n.[0] then
            n
]

[<Struct>]
type CollectSemanticsVisitor = {
    buffer: int ResizeArray
    lineMap: LineMap
    typeSystemEnv: TypeEnv
    mutable lastLine: int
    mutable lastStartChar: int
}
with
    interface ITypedSyntaxVisitor

type private T = KnownSemanticTokenTypes
type private M = KnownSemanticTokenModifiers

let writeTokenRange (this: _ byref) { start = start; end' = end' } =
    let (Position(line, startChar)) = LineMap.findPosition start this.lineMap
    let lastLine = this.lastLine
    let lastStartChar = this.lastStartChar

    this.buffer.Add(line - lastLine)
    this.buffer.Add(if line = lastLine then startChar - lastStartChar else startChar)
    this.buffer.Add(end' - start)

    this.lastLine <- line
    this.lastStartChar <- startChar

let private writeTokenSemantics (this: _ inref) tokenType tokenModifiers =
    this.buffer.Add(int<KnownSemanticTokenTypes> tokenType)
    this.buffer.Add(int<KnownSemanticTokenModifiers> tokenModifiers)

/// `...` `+` `#` …
let writeReservedTokenSemantics (this: _ byref) (ReservedVar(trivia = { span = span }; kind = kind)) _typeEnv =
    writeTokenRange &this span
    let struct(tokenType, tokenModifiers) =
        match kind with
        | TokenKind.Dot3 -> T.parameter, M.readonly
        | _ -> T.operator, M.``static``
    writeTokenSemantics &this tokenType tokenModifiers

let leafFlagModifiersSemantics leafFlags =
    let m = M.Empty
    let m = if leafFlags &&& L.Definition = L.Definition then m ||| M.definition else m
    let m = if leafFlags &&& L.Declaration = L.Declaration then m ||| M.declaration else m
    let m = if leafFlags &&& L.Modification = L.Modification then m ||| M.modification else m
    m

let leafFlagSemantics defaultType leafFlags =
    let t =
        match L._TypeMask &&& leafFlags with
        | L.Keyword -> T.keyword
        | L.Operator -> T.operator
        | L.TypeParameter -> T.typeParameter
        | L.Parameter -> T.parameter
        | L.Type -> T.``type``
        | L.Field -> T.property
        | L.Variable -> T.variable
        | _ -> defaultType

    let m = leafFlagModifiersSemantics leafFlags
    struct(t, m)

let writeDocumentReservedSemantics (this: _ byref) (D.Annotated(x, leaf)) =
    writeTokenRange &this x.trivia
    let struct(tokenType, tokenModifiers) = leafFlagSemantics T.operator leaf.leafFlags
    writeTokenSemantics &this tokenType tokenModifiers

let writeLiteralTokenSemantics (this: _ byref) { trivia = { Syntaxes.Trivia.span = span }; kind = kind } _type _typeEnv leafInfo =
    writeTokenRange &this span
    let struct(tokenType, tokenModifiers) =
        match kind with
        | S.Number _ -> T.number, M.Empty
        | S.String _ ->
            match leafInfo with
            | ValueSome { externalModulePath = ValueSome _ } -> T.``namespace``, M.Empty
            | _ -> T.string, M.Empty
        | _ -> T.keyword, M.Empty
    writeTokenSemantics &this tokenType tokenModifiers

let namedTypeSemantics (this: _ byref) typeConstant = function

    // `fun(…): (…)`
    | Type.Function this.typeSystemEnv (ValueSome _) -> ValueSome struct(T.``function``, M.Empty)
    | _ ->

    let types = this.typeSystemEnv.system

    // `boolean` `nil`
    if typeConstant = types.booleanConstant || typeConstant = types.nilConstant then
        ValueSome(T.``struct``, M.Empty)

    // `number`
    elif typeConstant = types.numberConstant then
        ValueSome(T.number, M.Empty)

    // `string`
    elif typeConstant = types.stringConstant then
        ValueSome(T.string, M.Empty)

    // `table<…,…>`
    elif typeConstant = types.tableConstant then
        ValueSome(T.``class``, M.Empty)

    /// `thread<…,…>`
    elif typeConstant = types.threadConstant then
        ValueSome(T.``function``, M.async)

    else
        ValueNone

let isSuperLike (lower, upper) super =

    // `number..` `(1 | 2)..`
    (TagSpace.isSubset lower super && TagSpace.isFull upper) ||

    // `..number` `..(1 | 2)`
    (TagSpace.isSubset upper super && TagSpace.isEmpty lower) ||

    // `1..number` `1..(1 | 2)`
    (TagSpace.isSubset lower super && TagSpace.isSubset upper super)

let constraintsSemantics { Token.kind = constraints } =
    match constraints with
    | InterfaceConstraint _ -> ValueSome struct(T.``interface``, M.Empty)
    | MultiElementTypeConstraint _ -> ValueNone
    | TagSpaceConstraint(lower, upper) ->
        ValueSome (
            if isSuperLike (lower, upper) TagSpace.allString then (T.string, M.Empty)
            elif isSuperLike (lower, upper) TagSpace.allNumber then (T.number, M.Empty)
            else (T.enum, M.Empty)
        )

let findTypeParameterConstraints id ps =
    ps
    |> List.tryPick (function
        | TypeParameter(_, id', c) when id' = id -> Some c
        | _ -> None
    )

// TODO: 高速化
let resolveTypeParameterConstraints typeEnv id =
    typeEnv.typeParameterOwners
    |> List.tryPick (function
        | Var(varType = { kind = TypeAbstraction(ps, _) }) ->
            findTypeParameterConstraints id ps

        | _ -> None
    )
    |> Option.unbox

let rec typeSemantics (this: _ byref) { Token.kind = type' } typeParameters typeEnv =
    match type' with

    // `fun(…) -> (…)` `nil` `table<…,…>`
    | NamedType(typeConstant, _) as t -> namedTypeSemantics &this typeConstant t

    // `{ x: …, … }`
    | InterfaceType _ -> ValueSome(T.``class``, M.Empty)

    // `a`
    | ParameterType id ->
        match findTypeParameterConstraints id typeParameters with
        | Some c -> constraintsSemantics c
        | _ ->

        match resolveTypeParameterConstraints typeEnv id with
        | ValueSome c -> constraintsSemantics c
        | _ -> ValueNone

    // `?a`
    | VarType v ->
        match v.target with
        | LuaChecker.Var(_, c) -> constraintsSemantics c
        | Assigned t -> typeSemantics &this t typeParameters typeEnv

    // `type(t) -> …`
    | TypeAbstraction(ps, t) -> typeSemantics &this t (ps @ typeParameters) typeEnv

let resolveLeafType leaf =
    let leaf = leaf.leafRare
    match leaf.declaration with
    | ValueSome d -> ValueSome d.scheme
    | _ ->

    match leaf.typeDefinition with
    | ValueSome d ->
        match d.typeKind with
        | TypeDefinitionKind.System _ -> ValueNone
        | TypeDefinitionKind.Alias t
        | TypeDefinitionKind.Variable(_, t) -> ValueSome t

    | _ ->

    leaf.type'

let leafTypeSemantics (this: _ byref) leaf =
    match resolveLeafType leaf with
    | ValueSome type' ->

        // TODO: 型環境を取得する
        let typeEnv = { TypeEnvironment.typeLevel = 0; TypeEnvironment.typeParameterOwners = [] }

        match typeSemantics &this type' [] typeEnv with
        | ValueSome((T.``function`` | T.number | T.string), _) as r -> r
        | _ -> ValueNone
    | _ -> ValueNone

let writeLeafSemantics (this: _ byref) defaultType leaf =
    let struct(tokenType, tokenModifiers) =
        match leafTypeSemantics &this leaf with
        | ValueSome(r, m) -> r, m ||| leafFlagModifiersSemantics leaf.leafFlags
        | _ -> leafFlagSemantics defaultType leaf.leafFlags

    writeTokenSemantics &this tokenType tokenModifiers

let identifierRepresentationToTokenModifiers = function
    | IdentifierRepresentation.Declaration -> M.declaration
    | IdentifierRepresentation.Definition -> M.definition
    | IdentifierRepresentation.Reference -> M.Empty

let writeVarTokenSemantics (this: _ byref) (Var(_, kind, repr, Name { trivia = { span = span } }, type', _)) typeEnv =
    writeTokenRange &this span
    let struct(tokenType, tokenModifiers) =
        match typeSemantics &this type' [] typeEnv with
        | ValueSome((T.``function`` | T.number | T.string) as t, m) ->
            t, m ||| identifierRepresentationToTokenModifiers repr

        | _ ->

        let t =
            match kind with
            | IdentifierKind.Variable -> T.variable
            | IdentifierKind.Parameter -> T.parameter
            | IdentifierKind.Field -> T.property
            | IdentifierKind.Method -> T.method

        t, identifierRepresentationToTokenModifiers repr

    writeTokenSemantics &this tokenType tokenModifiers

let writeDocumentIdentifierSemantics (this: _ byref) (D.Annotated(Name t, leaf)) =
    writeTokenRange &this t.trivia.span
    writeLeafSemantics &this T.typeParameter leaf

let writeDocumentFieldIdentifierSemantics (this: _ byref) (D.Annotated(key, leaf): LeafSemantics D.FieldIdentifier) =
    writeTokenRange &this key.trivia
    writeLeafSemantics &this T.property leaf

type CollectSemanticsVisitor with
    interface ITypedSyntaxVisitor with
        member v.Reserved(reserved, typeEnv) = writeReservedTokenSemantics &v reserved typeEnv
        member v.Literal(literal, type', typeEnv, leafInfo) = writeLiteralTokenSemantics &v literal type' typeEnv leafInfo
        member v.Var(var, typeEnv) = writeVarTokenSemantics &v var typeEnv

        member v.DocumentReserved x = writeDocumentReservedSemantics &v x
        member v.DocumentFieldSeparator x = writeDocumentReservedSemantics &v x
        member v.DocumentFieldVisibility x = writeDocumentReservedSemantics &v x
        member v.DocumentIdentifier x = writeDocumentIdentifierSemantics &v x
        member v.DocumentFieldIdentifier x = writeDocumentFieldIdentifierSemantics &v x
