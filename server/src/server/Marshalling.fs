module LuaChecker.Server.Marshalling
open Cysharp.Text
open LuaChecker
open LuaChecker.Server.Protocol
open LuaChecker.Syntax
open LuaChecker.Primitives
open LuaChecker.Text.Json
open LuaChecker.TypeSystem
open LuaChecker.TypedSyntaxes
open System
open System.IO


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
let showRelativePath context path =
    let root = Uri("file:///" + context.root.LocalPath).LocalPath
    Path.GetRelativePath(root, DocumentPath.toLocalPath path)

let (|Messages|) context = context.resources.DiagnosticMessages
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
    | K.DuplicateTag otherTag -> String.Format(m.DuplicateTag, showTagName otherTag)
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
    | K.RedeclarationOfSpecialGlobalVariable(name, oldKind, newKind) ->
        String.Format(
            m.RedeclarationOfSpecialGlobalVariable, name,
            showDeclKind context oldKind,
            showDeclKind context newKind
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

    | K.DuplicateTag otherTag ->
        match tryFindLocation context.documents path otherTag.trivia with
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
