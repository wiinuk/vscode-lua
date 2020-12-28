module LuaChecker.Analyzers.UnusedMemberAssemblyAnalyzer
open RichConsole
open RichConsole.Run.Operators
open FSharp.Compiler.SourceCodeServices
open Spectre.Console
open System
open System.Collections.Concurrent
open System.IO
open System.Reflection
open System.Reflection.Emit
open System.Reflection.PortableExecutable
open System.Reflection.Metadata
open System.Reflection.Metadata.Ecma335
type T = System.Reflection.Emit.OperandType
type H = System.Reflection.Metadata.HandleKind
let p, nl, ws = Run.styled, Run.lineBreak, Run.whitespace


let analyzerCategory = __SOURCE_FILE__
let defaultMessages = {|
    memberUnused = "{0} が使われていません"
    startAnalysisHeader = "------ 分析開始: ディレクトリ: {0} ------"
    endAnalysis = "------ 分析終了: 経過時間: {0} ------"
|}
let selectMessage resource selector =
    Option.defaultValue defaultMessages resource |> selector

let inline (!%) x = ((^From or ^To): (static member op_Implicit: ^From -> ^To) x)

let inline tryPick chooser source =
    let mutable e = (^EnumerableLike: (member GetEnumerator: unit -> _) source)
    let mutable result = ValueNone
    while
        begin
            if (^Enumerator: (member MoveNext: unit -> _) e) then
                let c = (^Enumerator: (member get_Current: unit -> _) e)
                match chooser c with
                | ValueSome _ as r ->
                    result <- r
                    false
                | _ ->
                    true
            else
                false
        end
        do ()
    result

let inline exists predicate source =
    tryPick (fun x -> if predicate x then ValueSome() else ValueNone) source
    |> ValueOption.isSome

let inline head source = tryPick ValueSome source |> ValueOption.get

type Severity =
    | Hint

type Location = {
    uri: string
    startLine: int
    startCharacter: int
    endLine: int
    endCharacter: int
}

type TypeId =
    | MissingSystemTypeId
    | TypeId of nameSpace: string * typeName: string
    | NestedTypeId of declaringType: TypeId * typeName: string

type Id =
    | MethodId of declaringType: TypeId voption * methodName: string
    | FieldId of declaringType: TypeId voption * fieldName: string

type DiagnosticKind =
    | MemberUnused of Id

type Diagnostic = {
    severity: Severity
    location: Location
    kind: DiagnosticKind
}

[<RequireQualifiedAccess>]
type LogLevel =
    | Silent
    | Error
    | Info
    | Debug
    | Trace

let mutable logLevel = LogLevel.Error
let isError<'a> = LogLevel.Error <= logLevel
let isDebug<'a> = LogLevel.Debug <= logLevel
let isInfo<'a> = LogLevel.Info <= logLevel
let isTrace<'a> = LogLevel.Trace <= logLevel

let showLocation l =
    try
        let full = Uri l.uri
        let relative = Uri($"{Environment.CurrentDirectory}{Path.DirectorySeparatorChar}").MakeRelativeUri full
        p (StyleExtensions.Link(Styles.sourceLocation, full.ToString())) $"{relative}"
    with _ ->
        p Styles.sourceLocation l.uri
    ++
    p Styles.sourceLocation $"({l.startLine}, {l.startCharacter})"

let rec showTypeId = function
    | TypeId("", name) -> p Styles.typeName name
    | TypeId(ns, name) -> p Styles.nameSpace ns ++ p Styles.delimiter "." ++ p Styles.typeName name
    | NestedTypeId(t, name) -> showTypeId t ++ p Styles.operator "+" ++ p Styles.typeName name
    | MissingSystemTypeId -> p Styles.missing "<system type>"

let showDeclaringType = function
    | ValueSome t -> showTypeId t ++ p Styles.operator "::"
    | _ -> Run.empty

let showId = function
    | MethodId(declaringType, name) -> showDeclaringType declaringType ++ p Styles.memberName name
    | FieldId(declaringType, name) -> showDeclaringType declaringType ++ p Styles.memberName name

let showKind messages = function
    | MemberUnused id ->
        Run.ofMarkup <| String.Format(selectMessage messages (fun x -> x.memberUnused), Run.markup (showId id))

let showSeverity s =
    let text =
        match s with
        | Hint -> "hint"

    let style =
        match s with
        | Hint -> Styles.hint

    p style text

let diagnosticCode (kind: DiagnosticKind) =
    $"AA{(let u, _ = Reflection.FSharpValue.GetUnionFields(kind, kind.GetType()) in u.Tag + 1):D04}"

let memberUnusedCode = diagnosticCode <| MemberUnused(FieldId(ValueNone, ""))

let printDiagnostic messages d =
    showLocation d.location ++
    p Styles.delimiter ":" ++ ws ++
    showSeverity d.severity ++ ws ++
    p Styles.label (diagnosticCode d.kind) ++
    p Styles.delimiter ":" ++ ws ++
    showKind messages d.kind
    |> Run.printLine

let documentName (metadata: MetadataReader) document =
    let name = metadata.GetDocument(document).Name
    if name.IsNil then null
    else metadata.GetString name

let sequencePointToLocation metadata (p: SequencePoint) =
    if p.IsHidden then ValueNone else

    ValueSome {
        uri = documentName metadata p.Document
        startLine = p.StartLine
        startCharacter = p.StartColumn
        endLine = p.EndLine
        endCharacter = p.EndColumn
    }

let findLocationFromILOffset metadata (debugInfo: MethodDebugInformation) offset =
    debugInfo.GetSequencePoints()
    |> tryPick (fun p ->
        if offset <= p.Offset
        then sequencePointToLocation metadata p
        else ValueNone
    )

let operandType =
    let operandToType = Map.ofSeq [
        for v in typeof<ILOpCode>.GetEnumValues() do
            let n = typeof<ILOpCode>.GetEnumName v
            let operation = v :?> ILOpCode
            let opCode =
                let n =
                    match n with
                    | "Tail" -> "Tailcall"
                    | n -> n
                typeof<OpCodes>.GetField(n, BindingFlags.Static ||| BindingFlags.Public ||| BindingFlags.IgnoreCase).GetValue(null) :?> OpCode
            operation, opCode.OperandType
    ]
    fun operator -> operandToType.[operator]

[<Struct>]
type OperationInfo = {
    offset: int
    operator: ILOpCode
}
type IVisitor =
    abstract MethodDefinition: operation: OperationInfo inref * operand: MethodDefinitionHandle -> bool
    abstract MemberReference: operation: OperationInfo inref * operand: MemberReferenceHandle -> bool
    abstract MethodSpecification: operation: OperationInfo inref * operand: MethodSpecificationHandle -> bool
    abstract FieldDefinition: operation: OperationInfo inref * operand: FieldDefinitionHandle -> bool
    abstract None: operation: OperationInfo inref -> bool

let visitILOperations (visitor: 'V byref when 'V :> IVisitor and 'V : struct) (body: MethodBodyBlock) =
    let mutable r = body.GetILReader()
    while
        begin
            if 0 < r.RemainingBytes then
                let operation = {
                    offset = r.Offset
                    operator =
                        match r.ReadByte() with
                        | 0xFEuy -> LanguagePrimitives.EnumOfValue(0xFE00us + uint16 (r.ReadByte()))
                        | x -> LanguagePrimitives.EnumOfValue(uint16 x)
                }
                match operandType operation.operator with
                | T.InlineMethod ->
                    let entity = MetadataTokens.EntityHandle <| r.ReadInt32()
                    if entity.IsNil then true else
                    match entity.Kind with
                    | H.MethodDefinition ->
                        visitor.MethodDefinition(&operation, MethodDefinitionHandle.op_Explicit entity)

                    | H.MethodSpecification ->
                        visitor.MethodSpecification(&operation, MethodSpecificationHandle.op_Explicit entity)

                    | H.MemberReference ->
                        visitor.MemberReference(&operation, MemberReferenceHandle.op_Explicit entity)

                    | k ->
                        failwith $"{k}"

                | T.InlineField ->
                    let entity = MetadataTokens.EntityHandle <| r.ReadInt32()
                    if entity.IsNil then true else
                    match entity.Kind with
                    | H.FieldDefinition ->
                        visitor.FieldDefinition(&operation, FieldDefinitionHandle.op_Explicit entity)

                    | H.MemberReference ->
                        visitor.MemberReference(&operation, MemberReferenceHandle.op_Explicit entity)

                    | k -> failwith $"{k}"

                | T.InlineI8
                | T.InlineR ->
                    r.Offset <- r.Offset + 8
                    true

                | T.InlineI
                | T.ShortInlineR
                | T.InlineBrTarget
                | T.InlineTok
                | T.InlineType
                | T.InlineSig
                | T.InlineString ->
                    r.Offset <- r.Offset + 4
                    true

                | T.InlineVar ->
                    r.Offset <- r.Offset + 2
                    true

                | T.ShortInlineI
                | T.ShortInlineBrTarget
                | T.ShortInlineVar ->
                    r.Offset <- r.Offset + 1
                    true

                | T.InlineSwitch ->
                    let count = r.ReadUInt32()
                    r.Offset <- r.Offset + int (count * 4u)
                    true

                | T.InlineNone ->
                    visitor.None &operation

                | _ ->
                    failwith $"%A{operation}"
                    true
            else
                false
            end
            do ()

let rec typeDefinitionId (metadata: MetadataReader) (typeDefinition: TypeDefinitionHandle) =
    let typeDefinition = metadata.GetTypeDefinition typeDefinition
    let declaringType = typeDefinition.GetDeclaringType()
    if declaringType.IsNil then
        TypeId(
            nameSpace = metadata.GetString typeDefinition.Namespace,
            typeName = metadata.GetString typeDefinition.Name
        )
    else
        NestedTypeId(
            declaringType = typeDefinitionId metadata declaringType,
            typeName = metadata.GetString typeDefinition.Name
        )

let typeReferenceId (metadata: MetadataReader) (typeReference: TypeReferenceHandle) =
    let t = metadata.GetTypeReference typeReference
    TypeId(metadata.GetString t.Namespace, metadata.GetString t.Name)

let genTypeIdProvider = { new ISignatureTypeProvider<_,_> with
    member _.GetArrayType(_, _) = MissingSystemTypeId
    member _.GetByReferenceType _ = MissingSystemTypeId
    member _.GetFunctionPointerType _ = MissingSystemTypeId
    member _.GetGenericInstantiation(genericType, _) = genericType
    member _.GetGenericMethodParameter(_, _) = MissingSystemTypeId
    member _.GetGenericTypeParameter(_, _) = MissingSystemTypeId
    member _.GetModifiedType(_, unmodifiedType, _) = unmodifiedType
    member _.GetPinnedType _ = MissingSystemTypeId
    member _.GetPointerType _ = MissingSystemTypeId
    member _.GetPrimitiveType _ = MissingSystemTypeId
    member _.GetSZArrayType _ = MissingSystemTypeId
    member _.GetTypeFromDefinition(metadata, definition, _rawTypeKind) = typeDefinitionId metadata definition
    member _.GetTypeFromReference(metadata, reference, _rawTypeKind) = typeReferenceId metadata reference
    member p.GetTypeFromSpecification(metadata, genericContext, specification, _rawTypeKind) =
        let t = metadata.GetTypeSpecification specification
        t.DecodeSignature(p, genericContext)
}
let methodDefinitionId (metadata: MetadataReader) (d: MethodDefinition) =
    let t = d.GetDeclaringType()
    let t = if t.IsNil then ValueNone else ValueSome <| typeDefinitionId metadata t
    MethodId(t, metadata.GetString d.Name)

let fieldDefinitionId (metadata: MetadataReader) (d: FieldDefinition) =
    let t = d.GetDeclaringType()
    let t = if t.IsNil then ValueNone else ValueSome <| typeDefinitionId metadata t
    FieldId(t, metadata.GetString d.Name)

let entityAsTypeId (metadata: MetadataReader) (typeDefinitionOrReferenceOrSpecification: EntityHandle) =
    if typeDefinitionOrReferenceOrSpecification.IsNil then ValueNone else

    match typeDefinitionOrReferenceOrSpecification.Kind with
    | H.TypeDefinition -> TypeDefinitionHandle.op_Explicit typeDefinitionOrReferenceOrSpecification |> typeDefinitionId metadata |> ValueSome
    | H.TypeReference -> TypeReferenceHandle.op_Explicit typeDefinitionOrReferenceOrSpecification |> typeReferenceId metadata |> ValueSome
    | H.TypeSpecification ->
        let parentType = TypeSpecificationHandle.op_Explicit typeDefinitionOrReferenceOrSpecification |> metadata.GetTypeSpecification
        parentType.DecodeSignature(genTypeIdProvider, ()) |> ValueSome

    | _ -> ValueNone

let addMethodDefinition (metadata: MetadataReader) m (results: ConcurrentDictionary<_,_>) =
    let m = metadata.GetMethodDefinition m
    match m.Attributes &&& MethodAttributes.MemberAccessMask with
    | MethodAttributes.Public
    | MethodAttributes.Assembly ->
        let id = methodDefinitionId metadata m
        ValueSome struct(id, results.TryAdd(id, ()))
    | _ -> ValueNone

let addMethodReference (metadata: MetadataReader) m (results: ConcurrentDictionary<_,_>) =
    let m = metadata.GetMemberReference m
    match m.GetKind() with
    | MemberReferenceKind.Method ->
        let name = metadata.GetString m.Name
        let id = MethodId(entityAsTypeId metadata m.Parent, name)
        ValueSome struct(id, results.TryAdd(id, ()))
    | _ -> ValueNone

[<Struct>]
type CollectMemberIdVisitor(metadata: MetadataReader, results: ConcurrentDictionary<Id, unit>) =
    static let showOperation op = $"IL_{op.offset:X04} {op.operator}"

    member _.MethodDefinition(op, m) =
        match addMethodDefinition metadata m results with
        | ValueSome(id, added) -> if isTrace then printfn $"    find {showOperation op} {showId id} %b{added}"
        | _ -> ()
        true

    member _.MemberReference(op, m) =
        match addMethodReference metadata m results with
        | ValueSome(id, added) -> if isTrace then printfn $"    find {showOperation op} {showId id} %b{added}"
        | _ -> ()
        true

    interface IVisitor with
        member _.None _ = true
        member v.MemberReference(operator, operand) = v.MemberReference(operator, operand)
        member v.MethodDefinition(operator, operand) = v.MethodDefinition(operator, operand)
        member v.MethodSpecification(operator, operand) =
            let m = metadata.GetMethodSpecification(operand).Method
            match m.Kind with
            | H.MethodDefinition -> v.MethodDefinition(operator, MethodDefinitionHandle.op_Explicit m)
            | H.MemberReference -> v.MemberReference(operator, MemberReferenceHandle.op_Explicit m)
            | k -> failwith $"{k}"

        member _.FieldDefinition(op, operand) =
            let f = metadata.GetFieldDefinition operand
            match f.Attributes &&& FieldAttributes.FieldAccessMask with
            | FieldAttributes.Public
            | FieldAttributes.Assembly ->
                let id = fieldDefinitionId metadata f
                let added = results.TryAdd(id, ())
                if isTrace then printfn $"    find {showOperation op} {showId id} %b{added}"
            | _ -> ()
            true

let attributeType (metadata: MetadataReader) (c: CustomAttribute) =
    let constructor = c.Constructor
    match constructor.Kind with
    | H.MemberReference ->
        let attributeType = metadata.GetMemberReference(MemberReferenceHandle.op_Explicit constructor).Parent
        match attributeType.Kind with
        | H.TypeReference -> TypeReferenceHandle.op_Explicit attributeType
        | _ -> TypeReferenceHandle()
    | _ -> TypeReferenceHandle()

let hasCompilerGeneratedAttribute (metadata: MetadataReader) entity =
    metadata.GetCustomAttributes entity
    |> exists (fun c ->
        let attribute = metadata.GetCustomAttribute c
        let attributeType = metadata.GetTypeReference <| attributeType metadata attribute
        metadata.GetString attributeType.Name = "CompilerGeneratedAttribute"
    )

let primitiveTypeCodeProvider = { new ICustomAttributeTypeProvider<_> with
    member _.GetPrimitiveType typeCode = typeCode
    member _.GetUnderlyingEnumType typeCode = typeCode

    member _.GetSZArrayType _ = LanguagePrimitives.EnumOfValue 0uy
    member _.GetSystemType() = LanguagePrimitives.EnumOfValue 0uy
    member _.GetTypeFromDefinition(_, _, _) = LanguagePrimitives.EnumOfValue 0uy
    member _.GetTypeFromReference(_, _, _) = LanguagePrimitives.EnumOfValue 0uy
    member _.GetTypeFromSerializedName _ = LanguagePrimitives.EnumOfValue 0uy
    member _.IsSystemType _ = false
}

// [<SuppressMessage("category", "checkId…")>]
let hasSuppressMessageAttribute (metadata: MetadataReader) entity expectedCategory expectedCheckId =
    metadata.GetCustomAttributes entity
    |> exists (fun c ->
        let attribute = metadata.GetCustomAttribute c
        let attribyteType = metadata.GetTypeReference <| attributeType metadata attribute
        if metadata.GetString attribyteType.Name <> "SuppressMessageAttribute" then false else

        let fixedArguments = attribute.DecodeValue(primitiveTypeCodeProvider).FixedArguments
        if fixedArguments.Length <> 2 then false else

        match fixedArguments.[0].Value, fixedArguments.[1].Value with
        | (:? string as category), (:? string as checkId) ->
            category = expectedCategory && checkId.StartsWith(expectedCheckId + "")
        | _ -> false
    )

let collectUsingMembers (module': PEReader) (metadata: MetadataReader) (task: ProgressTask) result =
    task.MaxValue <- double (metadata.MethodDefinitions.Count + metadata.CustomAttributes.Count)
    if isInfo then printfn $"collecting members in {metadata.MethodDefinitions.Count} methods"

    // メソッド内で使っているメンバーを集める
    for methodDefinitionHandle in metadata.MethodDefinitions do
        let methodDefinition = metadata.GetMethodDefinition methodDefinitionHandle
        let declaringType = metadata.GetTypeDefinition <| methodDefinition.GetDeclaringType()
        task.Description <-
            p Styles.typeName (metadata.GetString declaringType.Name) ++
            p Styles.delimiter "::" ++
            p Styles.memberName (metadata.GetString methodDefinition.Name)
            |> Run.markup

        task.Increment 1.

        match methodDefinition.RelativeVirtualAddress with

        // 抽象メソッド?
        | 0 -> ()

        | address ->
            let mutable visitor = CollectMemberIdVisitor(metadata, result)
            visitILOperations &visitor (module'.GetMethodBody address)

    // カスタム属性内で使っているメンバーを集める
    task.Description <- sprintf $"collection member in {metadata.CustomAttributes.Count} attributes"
    for attributeHandle in metadata.CustomAttributes do
        task.Increment 1.

        let attribute = metadata.GetCustomAttribute attributeHandle
        let constructor = attribute.Constructor
        match constructor.Kind with
        | H.MethodDefinition -> addMethodDefinition metadata (MethodDefinitionHandle.op_Explicit constructor) result |> ignore
        | H.MemberReference -> addMethodReference metadata (MemberReferenceHandle.op_Explicit constructor) result |> ignore
        | k -> failwith $"{k}"

let report (xs: _ ConcurrentBag) severity location kind = xs.Add {
    severity = severity
    location = location
    kind = kind
}

let emptyLocation = {
    uri = ""
    startLine = 0
    startCharacter = 0
    endLine = 0
    endCharacter = 0
}

let readDebugModuleOrNull (module': PEReader) =
    module'.ReadDebugDirectory()
    |> tryPick (fun d ->
        match d.Type with
        | DebugDirectoryEntryType.EmbeddedPortablePdb -> module'.ReadEmbeddedPortablePdbDebugDirectoryData d |> ValueSome
        | DebugDirectoryEntryType.CodeView ->

            // TODO:
            let codeView = module'.ReadCodeViewDebugDirectoryData d
            ValueNone

        | _ ->
            ValueNone
    )
    |> ValueOption.toObj

let findLocationFromILOffsetBy moduleFilePath debugMetadata methodDefinition' offset =
    let location =
        match debugMetadata with
        | None -> ValueNone
        | Some(debugMetadata: MetadataReader) ->
            let debugInfo = debugMetadata.GetMethodDebugInformation(methodDefinition': MethodDefinitionHandle)
            findLocationFromILOffset debugMetadata debugInfo offset

    match location with
    | ValueSome x -> x
    | _ ->
        { emptyLocation with
            uri = moduleFilePath
        }

let rec excludeByDeclaringTypes (metadata: MetadataReader) (typeDefinition: TypeDefinitionHandle) =
    if typeDefinition.IsNil then false else

    let t = metadata.GetTypeDefinition typeDefinition

    // public でなければ除外
    (t.Attributes &&& TypeAttributes.VisibilityMask <> TypeAttributes.Public) ||

    // 名前に '@' を含む型はコンパイラによって生成されたらしいので除外する
    metadata.GetString(t.Name).Contains "@" ||

    // [<SuppressMessage(…, …)>] で指定された型は除外
    hasSuppressMessageAttribute metadata !%typeDefinition analyzerCategory memberUnusedCode ||

    // 定義されている型を調査
    excludeByDeclaringTypes metadata (t.GetDeclaringType())

[<Struct>]
type GetterParseStage =
    | ExpectLdarg0
    | ExpectLdfld
    | ExpectRet
    | Return of bool

(*
    ldarg.0
    ldfld …
    ret
*)
[<Struct>]
type ParseUsedGetterBackingFieldVisitor(metadata: MetadataReader) =
    [<DefaultValue>] val mutable stage: GetterParseStage

    member v.Accept nextStage = v.stage <- nextStage; true
    member v.Done result = v.stage <- Return result; false
    member v.Failure() = v.Done false

    interface IVisitor with
        member v.None op =
            match v.stage, op.operator with
            | ExpectLdarg0, ILOpCode.Ldarg_0 -> v.Accept ExpectLdfld
            | ExpectRet, ILOpCode.Ret -> v.Done true
            | _ -> v.Failure()

        member v.FieldDefinition(op, _) =
            match v.stage, op.operator with
            | ExpectLdfld, ILOpCode.Ldfld -> v.Accept ExpectRet
            | _ -> v.Failure()

        member v.MemberReference(op, _) =
            match v.stage, op.operator with
            | ExpectLdfld, ILOpCode.Ldfld -> v.Accept ExpectRet
            | _ -> v.Failure()

        member v.MethodDefinition(_, _) = v.Failure()
        member v.MethodSpecification(_, _) = v.Failure()

[<Struct>]
type SetterParseStage =
    | ExpectLdarg0
    | ExpectLdarg1
    | ExpectStfld
    | ExpectRet
    | Return of bool
(*
    ldarg.0
    ldarg.1
    stfld …
    ret
*)
[<Struct>]
type ParseUsedSetterBackingFieldVisitor(metadata: MetadataReader) =
    [<DefaultValue>] val mutable stage: SetterParseStage
    member v.Accept stage = v.stage <- stage; true
    member v.Done r = v.stage <- Return r; false
    member v.Failure() = v.Done false

    interface IVisitor with
        member v.None op =
            match v.stage, op.operator with
            | ExpectLdarg0, ILOpCode.Ldarg_0 -> v.Accept ExpectLdarg1
            | ExpectLdarg1, ILOpCode.Ldarg_1 -> v.Accept ExpectStfld
            | ExpectRet, ILOpCode.Ret -> v.Done true
            | _ -> v.Failure()

        member v.FieldDefinition(op, _) =
            match v.stage, op.operator with
            | ExpectStfld, ILOpCode.Stfld -> v.Accept ExpectRet
            | _ -> v.Failure()

        member v.MemberReference(op, _) =
            match v.stage, op.operator with
            | ExpectStfld, ILOpCode.Stfld -> v.Accept ExpectRet
            | _ -> v.Failure()

        member v.MethodDefinition(_, _) = v.Failure()
        member v.MethodSpecification(_, _) = v.Failure()

let inline hasFlag set element =
    set &&& element = element

let isGetter (metadata: MetadataReader) (m: MethodDefinition) =
    hasFlag m.Attributes MethodAttributes.SpecialName &&
    metadata.GetString(m.Name).StartsWith "get_"

let isSetter (metadata: MetadataReader) (m: MethodDefinition) =
    hasFlag m.Attributes MethodAttributes.SpecialName &&
    metadata.GetString(m.Name).StartsWith "set_"

let isUsedGetterBackingField (module': PEReader) metadata m =
    if not (isGetter metadata m) || m.RelativeVirtualAddress = 0 then false else

    let body = module'.GetMethodBody m.RelativeVirtualAddress
    let mutable visitor =
        ParseUsedGetterBackingFieldVisitor(
            metadata = metadata,
            stage = GetterParseStage.ExpectLdarg0
        )

    visitILOperations &visitor body
    match visitor.stage with
    | GetterParseStage.Return x -> x
    | _ -> false

let isUsedSetterBackingField (module': PEReader) metadata m =
    if not (isSetter metadata m) || m.RelativeVirtualAddress = 0 then false else

    let body = module'.GetMethodBody m.RelativeVirtualAddress
    let mutable visitor =
        ParseUsedSetterBackingFieldVisitor(
            metadata = metadata,
            stage = SetterParseStage.ExpectLdarg0
        )
    visitILOperations &visitor body
    match visitor.stage with
    | SetterParseStage.Return x -> x
    | _ -> false

let findParentProperty (metadata: MetadataReader) (h: MethodDefinitionHandle) =
    let m = metadata.GetMethodDefinition h
    if not (isGetter metadata m || isSetter metadata m) then ValueNone else

    let declaringType = m.GetDeclaringType()
    if declaringType.IsNil then ValueNone else

    let declaringType = metadata.GetTypeDefinition declaringType
    declaringType.GetProperties()
    |> tryPick (fun p ->
        let property = metadata.GetPropertyDefinition p
        let accessors = property.GetAccessors()
        if accessors.Getter = h || accessors.Setter = h then
            ValueSome p
        else
            ValueNone
    )

let excludeByParentProperty (metadata: MetadataReader) (h: MethodDefinitionHandle) =
    match findParentProperty metadata h with
    | ValueNone -> false
    | ValueSome property ->
        hasSuppressMessageAttribute metadata !%property analyzerCategory memberUnusedCode

let isExcludeMethod (metadata: MetadataReader) entryPointHandle (h: MethodDefinitionHandle) =

    // Main は除外
    entryPointHandle = h ||

    let m = metadata.GetMethodDefinition h
    let a = m.Attributes

    // public でないメソッドは除外
    (a &&& MethodAttributes.MemberAccessMask <> MethodAttributes.Public) ||

    // virtual メソッドは除外
    hasFlag a MethodAttributes.Virtual ||

    // 定義されている型によって除外されているか
    excludeByDeclaringTypes metadata (m.GetDeclaringType()) ||

    // [CompilerGenerated] は除外
    hasCompilerGeneratedAttribute metadata !%h ||

    // 名前に '@' を含むメソッドはコンパイラによって生成されたらしいので除外する
    metadata.GetString(m.Name).Contains "@" ||

    // [<SuppressMessage(…, …)>] で指定されたメンバは除外
    hasSuppressMessageAttribute metadata !%h analyzerCategory memberUnusedCode ||

    // 定義されたプロパティによって除外されているか
    excludeByParentProperty metadata h

type ModuleDiagnosticMetadata = {
    module': PEReader
    debugMetadata: MetadataReader option
    metadata: MetadataReader
}
let lineTokens state (tokenizer: FSharpSourceTokenizer) line (result: _ ResizeArray) =
    let mutable state = state
    let lineTokenizer = tokenizer.CreateLineTokenizer line
    while
        match lineTokenizer.ScanToken state with
        | Some token, state' -> result.Add token; state <- state'; true
        | _, state' -> state <- state'; false
        do ()
    state

let fsharpSourceIncludesInline location tokenizer tokens =
    try
        let path = Uri(location.uri).LocalPath
        match Path.GetExtension path with
        | ".fs"
        | ".fsx" ->
            let startLine = max (location.startLine - 1) 1
            let endLine = location.endLine + 1
            File.ReadLines path
            |> Seq.skip (startLine - 1)
            |> Seq.truncate (endLine - startLine)
            |> Seq.scan (fun struct(state, _) line ->
                try
                    let state = lineTokens state tokenizer line tokens
                    state, tokens |> exists (fun x -> x.TokenName = "INLINE")
                finally
                    tokens.Clear()
            ) (FSharpTokenizerLexState.Initial, false)
            |> Seq.exists (fun struct(_, x) -> x)
        | _ -> false

    with _ -> false

let publicUnusedMembersDiagnosticsBy (usingMemberIds: ConcurrentDictionary<_,_>) moduleFilePath metadata (task: ProgressTask) diagnostics =
    let { module' = module'; debugMetadata = debugMetadata; metadata = metadata } = metadata

    let entryPointHandle =
        let headers = module'.PEHeaders
        if headers.IsExe then
            MetadataTokens.MethodDefinitionHandle headers.CorHeader.EntryPointTokenOrRelativeVirtualAddress
        else
            MetadataTokens.MethodDefinitionHandle 0

    let tokenizer = FSharpSourceTokenizer([], None)
    let tokens = ResizeArray()

    // モジュールの全てのメソッドを列挙
    task.MaxValue <- double metadata.MethodDefinitions.Count
    for methodDefinitionHandle in metadata.MethodDefinitions do
        let methodDefinition = metadata.GetMethodDefinition methodDefinitionHandle
        task.Description <- metadata.GetString methodDefinition.Name
        task.Increment 1.

        if isExcludeMethod metadata entryPointHandle methodDefinitionHandle then () else

        let id = methodDefinitionId metadata methodDefinition
        if
            // メソッドか使われているか
            usingMemberIds.ContainsKey id ||

            // メソッドが使われていなくても、プロパティのバッキングフィールドが使われているならメソッドが使われていることにする
            isUsedGetterBackingField module' metadata methodDefinition ||
            isUsedSetterBackingField module' metadata methodDefinition
        then ()
        else

        let location = findLocationFromILOffsetBy moduleFilePath debugMetadata methodDefinitionHandle 0

        // F# ソースが inline トークンを含むなら除外
        if fsharpSourceIncludesInline location tokenizer tokens then () else

        // 使われていなければ報告
        report diagnostics Hint location <| MemberUnused id

let openPEFile path =
    let file = new FileStream(path, FileMode.Open, FileAccess.Read, FileShare.ReadWrite)
    new PEReader(file)

let setDescriptionWithTime text (task: ProgressTask) =
    let time = if task.ElapsedTime.HasValue then $"{task.ElapsedTime.Value.Milliseconds:G}" else "???"
    task.Description <- $"{text}: {time,4}ms"

let nullConsole() =
    let cursor = { new IAnsiConsoleCursor with
        member _.Move(_, _) = ()
        member _.SetPosition(_, _) = ()
        member _.Show _ = ()
    }
    let input = { new IAnsiConsoleInput with
        member _.ReadKey _ = ConsoleKeyInfo()
    }
    { new IAnsiConsole with
        member _.Capabilities = Capabilities(true, ColorSystem.TrueColor, false, false)
        member _.Encoding = System.Text.Encoding.UTF8
        member _.Height = 1000
        member _.Width = 1000
        member _.Write _ = ()
        member _.Clear _ = ()
        member _.Cursor = cursor
        member _.Input = input
        member _.Pipeline = new Rendering.RenderPipeline()
    }

let checkPublicUnusedMembers diagnostics producerAssemblyPaths consumerAssemblyPaths =
    let usingMemberIds = ConcurrentDictionary()
    let console = if isInfo then AnsiConsole.Console else nullConsole()

    console.Progress().Start(fun progress ->

        // 消費アセンブリで使われているメンバーを収集
        consumerAssemblyPaths
        |> Seq.toArray
        |> Array.Parallel.iter (fun path ->
            if isInfo then printfn $"{path}"
            let task = progress.AddTask(Path.GetFileName(path + ""))
            use module' = openPEFile path
            let metadata = module'.GetMetadataReader()
            collectUsingMembers module' metadata task usingMemberIds
            setDescriptionWithTime (Path.GetFileName path) task
        )
    )

    if isTrace then for m in usingMemberIds do printfn $"using {showId m.Key}"
    if isInfo then printfn $"uses {usingMemberIds.Count} unique members"

    // 生産アセンブリで使われていないメンバーを診断
    console.Progress().Start(fun progress ->
        producerAssemblyPaths
        |> Seq.toArray
        |> Array.Parallel.iter (fun path ->
            let task = progress.AddTask(Path.GetFileName(path + ""))

            use module' = openPEFile path
            use debugModuleOrNull = readDebugModuleOrNull module'
            let debugMetadata = if not (isNull debugModuleOrNull) then debugModuleOrNull.GetMetadataReader() |> Some else None
            let metadata = module'.GetMetadataReader()
            let moduleMetadata = {
                module' = module'
                debugMetadata = debugMetadata
                metadata = metadata
            }
            publicUnusedMembersDiagnosticsBy usingMemberIds path moduleMetadata task diagnostics
            setDescriptionWithTime (Path.GetFileName path) task
        )
    )
