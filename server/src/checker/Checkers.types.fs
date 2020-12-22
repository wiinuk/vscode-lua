namespace LuaChecker
open LuaChecker.TypedSyntaxes
open LuaChecker.TypeSystem
open LuaChecker.Primitives
open System.Collections.Immutable
module S = Syntaxes


[<RequireQualifiedAccess>]
type Severity =
    | Info
    | Warning
    | Error

[<RequireQualifiedAccess>]
type DiagnosticKind =
    | ParseError of Syntax.ParseError
    | UnifyError of UnifyError
    | ReturnValueIgnored
    | NameNotFound of string
    | IndirectGlobalRequireUse
    | ModuleNotFound of moduleName: string * searchedModulePaths: DocumentPath list
    | ExternalModuleError of modulePath: DocumentPath * diagnostic: Diagnostic
    | RecursiveModuleReference of modulePath: DocumentPath
    | UnrecognizableGlobalPackageUse
    | TypeNameNotFound of string
    | TypeArityMismatch of expectedArity: int * actualArity: int
    | DuplicateFieldKey of FieldKey * otherFieldSpan: Span
    | RedeclarationOfSpecialGlobalVariable of name: string * oldKind: DeclarationFeatures * newKind: DeclarationFeatures
    | RedeclarationOfBasicType of SystemTypeCode
    | RedeclarationOfTypeVariable of name: string * oldTypeLocations: Location list
    | UndeterminedGlobalVariableEnvironment of modulePath: DocumentPath * additionalGlobals: Map<string, NonEmptyList<Declaration>>
    | GlobalNameCollision of name: string * decl1: Declaration * decl2: Declaration * decls: Declaration list
    | GlobalTypeCollision of name: string * type1: TypeDefinition * type2: TypeDefinition * types: TypeDefinition list
    | UnrecognizedFeatureName of featureName: string
    | UnexpectedMultiType
    | RequireMultiType
    | DuplicateTag of otherTag: HEmpty Syntax.Documents.Tag
    | FieldParentTagNotFound
    | GenericTagParentSyntaxNotFound
    | TypeTagParentSyntaxNotFound

and Diagnostic = Diagnostic of Span * Severity * DiagnosticKind
module Diagnostic =
    let error span kind = Diagnostic(span, Severity.Error, kind)
    let warn span kind = Diagnostic(span, Severity.Warning, kind)
    let info span kind = Diagnostic(span, Severity.Info, kind)

type SemanticModel = {
    syntaxTree: S.Block
    typedTree: Chunk
}
type SourceLink =
    | InFs of path: DocumentPath * lastWriteTime: System.DateTime
    | InMemory of source: string * version: int

type AnalyticsStage =
    | BeforeParse
    | AnalysisComplete of SemanticModel * diagnostics: Diagnostic seq

[<Struct>]
type SourceFileAnalytics = {
    stage: AnalyticsStage
    source: SourceLink
}
type FileSystem = {
    readAllText: DocumentPath -> string
    writeAllText: struct(DocumentPath * string) -> unit
    deleteFile: DocumentPath -> unit
    lastWriteTime: DocumentPath -> System.DateTime
    enumerateFiles: DocumentPath -> DocumentPath seq
}
module FileSystem =
    open System.Collections.Generic
    open System.IO

    let systemIO = {
        readAllText = fun x -> DocumentPath.toPathOrFail x |> File.ReadAllText
        lastWriteTime = fun x -> DocumentPath.toPathOrFail x |> File.GetLastWriteTime
        writeAllText = fun struct(p, c) -> File.WriteAllText(DocumentPath.toPathOrFail p, c)
        deleteFile = fun x -> DocumentPath.toPathOrFail x |> File.Delete
        enumerateFiles = fun x ->
            Directory.EnumerateFiles(DocumentPath.toPathOrFail x, "*", EnumerationOptions())
            |> Seq.map DocumentPath.ofPath
    }
    let memory() =
        let gate = obj()
        let mutable lastWriteTime = System.DateTime.MinValue
        let backingStore = Dictionary()
        {
            readAllText = fun x -> lock gate <| fun _ -> snd backingStore.[x]
            writeAllText = fun struct(p, c) -> lock gate <| fun _ ->
                backingStore.[p] <- (lastWriteTime, c)
                lastWriteTime <- lastWriteTime.AddMilliseconds 1.

            deleteFile = fun x -> lock gate <| fun _ -> backingStore.Remove x |> ignore
            lastWriteTime = fun x -> lock gate <| fun _ -> fst backingStore.[x]
            enumerateFiles = fun x -> lock gate <| fun _ -> seq {
                let rootPath = DocumentPath.toPathOrFail x
                for kv in backingStore do

                    // NOTE: テスト用の雑実装
                    match DocumentPath.toPathOrNone kv.Key with
                    | ValueSome path when path.StartsWith rootPath -> kv.Key
                    | _ -> ()
            }
        }

type TypeCache = {
    /// ...(type(a: nil..) -> a)
    nilOrUpperMultiElementConstraint: Constraints'
    /// ..boolean
    booleanOrLowerConstraint: Constraints'
    /// ..number
    numberOrLowerConstraint: Constraints'
    /// ..string
    stringOrLowerConstraint: Constraints'
    /// ..(number | string)
    numberOrStringOrLowerConstraint: Constraints'
    /// ..(string | table)
    stringOrTableOrLowerConstraint: Constraints'
    /// boolean..
    booleanOrUpperConstraint: Constraints'
    /// number..
    numberOrUpperConstraint: Constraints'
    /// string..
    stringOrUpperConstraint: Constraints'
}
module TypeCache =
    module private Constraints =
        /// e.g. `..(10 | 11)`
        let tagOrLower upperBound = TagSpaceConstraint(lowerBound = TagSpace.empty, upperBound = upperBound)
        /// e.g. `(10 | 11)..`
        let tagOrUpper lowerBound = TagSpaceConstraint(lowerBound = lowerBound, upperBound = TagSpace.full)

    /// type(displayName: lowerBound..upperBound) -> displayName
    let private tagSpaceTypeAbs types displayName (lowerBound, upperBound) =
        let b = TypeParameterId.createNext types.valueKind
        let c = TagSpaceConstraint(lowerBound = lowerBound, upperBound = upperBound) |> Constraints.makeWithEmptyLocation
        TypeAbstraction([TypeParameter(displayName, b, c)], ParameterType b |> Type.makeWithEmptyLocation)

    /// type(displayName: lowerBound..) -> displayName
    let private tagOrUpperTypeAbs types displayName lowerBound =
        tagSpaceTypeAbs types displayName (lowerBound, TagSpace.full)

    let create types = {
        nilOrUpperMultiElementConstraint = tagOrUpperTypeAbs types "nil" TagSpace.nil |> Type.makeWithEmptyLocation |> MultiElementTypeConstraint
        booleanOrLowerConstraint = Constraints.tagOrLower TagSpace.allBoolean
        numberOrLowerConstraint = Constraints.tagOrLower TagSpace.allNumber
        stringOrLowerConstraint = Constraints.tagOrLower TagSpace.allString
        numberOrStringOrLowerConstraint = Constraints.tagOrLower <| TagSpace.allString + TagSpace.allNumber
        stringOrTableOrLowerConstraint = Constraints.tagOrLower <| TagSpace.allString + TagSpace.allTable
        booleanOrUpperConstraint = Constraints.tagOrUpper TagSpace.allBoolean
        numberOrUpperConstraint = Constraints.tagOrUpper TagSpace.allNumber
        stringOrUpperConstraint = Constraints.tagOrUpper TagSpace.allString
    }

type TopEnv = {
    typeSystem: TypeSystem
    derivedTypes: TypeCache
    initialGlobalEnv: Env
    packagePath: string
}
module TopEnv =
    open System
    let parseLuaPath (luaPath: string) = [
        for p in luaPath.Split ';' do
            match p with
            | null
            | "" -> ()
            | _ -> p
    ]
    let luaPathDefault platform luaExeDirectory =
        match platform with
        | PlatformID.Win32NT
        | PlatformID.Win32S
        | PlatformID.Win32Windows
        | PlatformID.WinCE ->
            match luaExeDirectory with
            | Some exe -> sprintf @"./?.lua;%s/lua/?.lua;%s/lua/?/init.lua;%s/?.lua;%s/?/init.lua" exe exe exe exe
            | _ -> ".\\?.lua;"
        | _ ->
            let share = "/usr/local/share/lua/5.1/"
            let lib = "/usr/local/lib/lua/5.1/"
            sprintf "./?.lua;%s?.lua;%s?/init.lua;%s?.lua;%s?/init.lua" share share lib lib

    let packagePath luaPath platform luaExeDirectory =
        let defaultLuaPath = luaPathDefault platform luaExeDirectory
        match luaPath with
        | None -> defaultLuaPath
        | Some(luaPath: string) -> luaPath.Replace(";;", ";" + defaultLuaPath + ";")

type ProjectRareUpdate = {
    initialGlobal: TopEnv
    fileSystem: FileSystem
}

[<Struct>]
type HashMap<'K,'V> = HashMap of ImmutableDictionary<'K,'V>
module HashMap =
    [<Sealed; AbstractClass>]
    type private EmptyHashMapHolder<'K,'V> when 'K : equality private () =
        static let value: HashMap<'K,'V> = HashMap <| ImmutableDictionary.Create LanguagePrimitives.FastGenericEqualityComparer
        static member Value = value

    [<GeneralizableValue>]
    let empty<'K,'V when 'K : equality> = EmptyHashMapHolder<'K,'V>.Value
    let emptyWith comparer = HashMap <| ImmutableDictionary.Create comparer

    let add key value (HashMap map) = HashMap <| map.SetItem(key, value)
    let tryFind key (HashMap map) =
        let mutable result = Unchecked.defaultof<_>
        if map.TryGetValue(key, &result) then ValueSome result
        else ValueNone

    let remove key (HashMap map) = HashMap <| map.Remove key

    let inline fold folder state (HashMap map) =
        let mutable e = map.GetEnumerator()
        let mutable s = state
        while e.MoveNext() do
            let kv = e.Current
            s <- folder s kv.Key kv.Value
        s

[<Struct>]
type Project = {
    pathToSourceFile: HashMap<DocumentPath, SourceFileAnalytics>
    projectRare: ProjectRareUpdate
}

type EnvNoUpdate<'Scope,'RootScope> = {
    types: TypeSystem
    typeCache: TypeCache
    diagnostics: Diagnostic ResizeArray
    filePath: DocumentPath
    source: string Lazy
    project: Local<'Scope, Project>
    ancestorModulePaths: Local<'Scope, DocumentPath Set>

    defaultGlobalEnv: Env
    additionalGlobalEnv: Local<'Scope, Env>

    visitedSources: Local<'RootScope, DocumentPath Set>
}
type EnvRareUpdate<'Scope,'RootScope> = {
    nameToType: Map<string, TypeDefinition>

    temporaryTypeVarLevel: int
    temporaryTypeVarEnv: Map<string, Type> ref

    isChunkTop: bool
    typeLevel: int
    returnType: Type
    varArgType: Type
    selfType: TypeDefinition voption
    packagePath: string
    suppressDiagnostics: bool

    noUpdate: EnvNoUpdate<'Scope,'RootScope>
}
[<Struct>]
type CheckerEnv<'Scope,'RootScope> = {
    nameToDeclaration: Map<string, Declaration>
    rare: EnvRareUpdate<'Scope,'RootScope>
}
module CheckerEnv =
    type private K = DiagnosticKind

    module TypeNames =
        let fromFieldKey = function
            | FieldKey.String x -> ValueSome x
            | _ -> ValueNone

        let lostByError = "lost"
        let implicitMultiVar = ""
        let constrainedType = "c"
        let classParent = "parent"
        let fieldKeyValueInterface = "field"
        let multiType1 = "first"
        let multiRest = "rest"
        let multiRestNils = "nils"
        let indexSelf = "self"
        let functionResult = "result"
        let arrayKey = "k"
        let arrayValue = "v"
        let multiElement = "e"
        let multiElements = "es"
        let fieldValue = "v"
        let multiOverflow = "overflow"
        let condition = "condition"
        let forVar = "var"
        let forStart = "start"
        let forStop = "stop"
        let forStep = "step"
        let forInState = "state"
        let forInFirstVar = "value"
        let forInRestVars = "values"

    let types env = env.rare.noUpdate.types
    let typeEnv env =
        let env = env.rare.noUpdate
        {
            system = env.types
            stringTableTypes = env.defaultGlobalEnv.stringMetaTableIndexType @ env.additionalGlobalEnv.Value.stringMetaTableIndexType
        }
    let (|Types|) env = types env
    let (|TypeEnv|) env = typeEnv env
    let typeCache env = env.rare.noUpdate.typeCache
    let (|TypeCache|) env = typeCache env

    let report { rare = env } d = if not env.suppressDiagnostics then env.noUpdate.diagnostics.Add d
    let reportError env span kind = report env <| Diagnostic.error span kind
    let reportWarn env span kind = report env <| Diagnostic.warn span kind
    let reportInfo env span kind = report env <| Diagnostic.info span kind
    let reportIfUnifyError env span t1 t2 =
        match Type.unify (typeEnv env) t1 t2 with
        | ValueSome e -> reportError env span <| K.UnifyError e
        | _ -> ()

    let inline private resolve1OrReportCore makeError span n env map =
        match Map.tryFind n map with
        | ValueSome(NonEmptyList(d, [])) -> ValueSome d
        | ValueSome(NonEmptyList(d1, d2::ds)) ->
            reportError env span <| makeError(n, d1, d2, ds)
            ValueSome d1
        | _ -> ValueNone

    let private resolveName1OrReport span n env map = resolve1OrReportCore K.GlobalNameCollision span n env map
    let private resolveType1OrReport span n env map = resolve1OrReportCore K.GlobalTypeCollision span n env map

    let resolveGlobalVariable span n env =
        let env' = env.rare.noUpdate
        match resolveName1OrReport span n env env'.additionalGlobalEnv.Value.names with
        | ValueSome d -> ValueSome d
        | _ -> resolveName1OrReport span n env env'.defaultGlobalEnv.names

    let resolveVariable span n env =
        match Map.tryFind n env.nameToDeclaration with
        | ValueSome _ as r -> r
        | _ -> resolveGlobalVariable span n env

    let resolveType span n env =
        match Map.tryFind n env.rare.nameToType with
        | ValueSome _ as r -> r
        | _ ->

        let env' = env.rare.noUpdate
        match resolveType1OrReport span n env env'.additionalGlobalEnv.Value.types with
        | ValueSome _ as r -> r
        | _ -> resolveType1OrReport span n env env'.defaultGlobalEnv.types

    let extend location s k r n t env = {
        env with
            nameToDeclaration =
                env.nameToDeclaration
                |> Map.add n {
                    declarationFeatures = DeclarationFeatures.NoFeatures
                    declarationScope = s
                    declarationKind = k
                    declarationRepresentation = r
                    scheme = t
                    location = location
                }
    }

    let extendType name definition env =
        { env with
            rare = { env.rare with nameToType = Map.add name definition env.rare.nameToType }
        }

    let enterChunkLocal env =
        { env with rare = { env.rare with isChunkTop = false } }

    let enterTemporaryTypeVarNameScope env =
        { env with
            rare = {
            env.rare with
                temporaryTypeVarLevel = env.rare.temporaryTypeVarLevel + 1
                temporaryTypeVarEnv = ref Map.empty
            }
        }

    let enterTypeScope env = { env with rare = { env.rare with typeLevel = env.rare.typeLevel + 1 } }

    let newVarTypeWith env displayName kind c = Type.newVarWith displayName env.rare.typeLevel kind c
    let newVarType env displayName kind = newVarTypeWith env displayName kind Constraints.any

    let newValueVarTypeWith env displayName c = newVarTypeWith env displayName (types env).valueKind c
    let newValueVarType env displayName = newValueVarTypeWith env displayName Constraints.any

    let newMultiVarTypeWith env displayName c = newVarTypeWith env displayName (types env).multiKind c
    let newMultiVarType env displayName = newMultiVarTypeWith env displayName Constraints.any

    let isMultiKind (TypeEnv env) t = Type.kind env t = env.system.multiKind
    let isValueKind (TypeEnv env) t = Type.kind env t = env.system.valueKind

    let sourceLocation env span = [Location(env.rare.noUpdate.filePath, span)]

    let reportIfNotMultiKind env span m =
        if isMultiKind env m then m else

        reportError env span K.RequireMultiType
        newMultiVarType env TypeNames.lostByError
        |> Type.makeWithLocation (sourceLocation env span)

    let reportIfNotValueKind env span t =
        if isValueKind env t then t else

        reportError env span K.UnexpectedMultiType
        newValueVarType env TypeNames.lostByError
        |> Type.makeWithLocation (sourceLocation env span)

[<Struct>]
type StatState = {
    isImplicitReturn: bool
}
module StatState =
    let merge s1 s2 = { isImplicitReturn = s1.isImplicitReturn || s2.isImplicitReturn }

[<Struct>]
type TypeResolveEnv<'EnvScope,'RootScope> = {
    mutable implicitVariadicParameterType: Type option
    env: CheckerEnv<'EnvScope,'RootScope>
}

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Type =
    open LuaChecker.Syntax
    type private K = DiagnosticKind
    module D = Documents

    let getOrNewVar newVar i ts =
        match List.tryItem i ts with
        | None -> newVar()
        | Some struct(t, _) -> t

    let alignArity newVar expectedArity ts = [
        for i in 0..expectedArity-1 ->
            getOrNewVar newVar i ts
    ]
    let typeNameAsTypeVar (env: _ inref) (Name({ kind = name } as n)) =
        let vars = env.env.rare.temporaryTypeVarEnv
        match Map.tryFind name vars.Value with
        | ValueSome t -> t
        | _ ->

        let t =
            Type.newVar name env.env.rare.temporaryTypeVarLevel (CheckerEnv.types env.env).valueKind
            |> Type.makeWithLocation (CheckerEnv.sourceLocation env.env n.trivia.span)

        vars.Value <- Map.add name t vars.Value
        t

    let (|TypeVarLikeName|) name =
        String.length name = 1 ||
        (name.[0] = 'T' && not (System.Char.IsLower name.[1]))

    let getImplicitMultiVarType (env: _ byref) span =
        match env.implicitVariadicParameterType with
        | Some v -> v
        | None ->
            let v =
                CheckerEnv.newMultiVarType env.env CheckerEnv.TypeNames.implicitMultiVar
                |> Type.makeWithLocation (CheckerEnv.sourceLocation env.env span)
            env.implicitVariadicParameterType <- Some v
            v

    let resolveMultiVar (env: _ byref) span = function

        // 名前なしの複型変数 `...` は、暗黙的にスコープで共通の複型変数を指す
        | None -> getImplicitMultiVarType &env span

        // 名前付きの複型変数 `M...`
        | Some(D.Annotated(Name { kind = name; trivia = { span = nameSpan } }, _)) ->

        match CheckerEnv.resolveType nameSpan name env.env with
        | ValueSome d ->
            match d.typeKind with
            | TypeDefinitionKind.Variable(_, m)
            | TypeDefinitionKind.Alias m  -> CheckerEnv.reportIfNotMultiKind env.env nameSpan m
            | TypeDefinitionKind.System _ ->
                CheckerEnv.reportError env.env nameSpan K.RequireMultiType
                CheckerEnv.newMultiVarType env.env CheckerEnv.TypeNames.lostByError
                |> Type.makeWithLocation (CheckerEnv.sourceLocation env.env nameSpan)
        | _ ->

        let vars = env.env.rare.temporaryTypeVarEnv
        match Map.tryFind name vars.Value with

        // スコープにある名前だった
        | ValueSome t -> CheckerEnv.reportIfNotMultiKind env.env nameSpan t
        | _ ->

        // スコープにない名前だった
        let t =
            Type.newVar name env.env.rare.temporaryTypeVarLevel (CheckerEnv.types env.env).multiKind
            |> Type.makeWithLocation (CheckerEnv.sourceLocation env.env nameSpan)

        vars.Value <- Map.add name t vars.Value
        t

    let inline usingByrefAsRef (location: _ byref) scope =
        // TODO: pool
        let temp = ref location
        try scope temp
        finally location <- !temp

    let reportArityMismatch env (Name name) expectedArity actualArity =
        let e = K.TypeArityMismatch(expectedArity = expectedArity, actualArity = actualArity)
        CheckerEnv.reportError env name.trivia.span e

    let systemTableType (CheckerEnv.Types types as env) name typeArgs =
        match typeArgs with
        | [struct(k, _); struct(v, _)] when CheckerEnv.isValueKind env k && CheckerEnv.isValueKind env v -> types.table(k, v)
        | _ ->

        reportArityMismatch env name 2 (List.length typeArgs)

        let newVar() =
            CheckerEnv.newVarType env CheckerEnv.TypeNames.lostByError types.valueKind
            |> Type.makeWithLocation (CheckerEnv.sourceLocation env <| Name.measure name)

        types.table(
            getOrNewVar newVar 0 typeArgs,
            getOrNewVar newVar 1 typeArgs
        )

    let systemThreadType (CheckerEnv.Types types as env) name typeArgs =
        match typeArgs with
        | [struct(i, _); struct(o, _)] when CheckerEnv.isMultiKind env i && CheckerEnv.isMultiKind env o -> types.thread(i, o)
        | _ ->

        reportArityMismatch env name 2 (List.length typeArgs)
        let newVar() =
            CheckerEnv.newMultiVarType env CheckerEnv.TypeNames.lostByError
            |> Type.makeWithLocation (CheckerEnv.sourceLocation env <| Name.measure name)

        types.thread(
            getOrNewVar newVar 0 typeArgs,
            getOrNewVar newVar 1 typeArgs
        )

    let unifyApplications env name typeParameterToType typeWithSpans =
        let rec aux remainingVs remainingTs =
            match remainingVs, remainingTs with
            | [], [] -> ()
            | struct(_, v)::vs, struct(t, span)::ts ->
                match Type.unify (CheckerEnv.typeEnv env) v t with
                | ValueSome e -> CheckerEnv.reportError env span <| K.UnifyError e
                | _ -> ()

                aux vs ts

            | _ ->
                reportArityMismatch env name (List.length typeParameterToType) (List.length typeWithSpans)

        aux typeParameterToType typeWithSpans

    let buildTypeOfAliasDefinition env name d typeArgs =
        let struct(vs, instantiatedType) = Scheme.instantiate env.rare.typeLevel d
        match vs, typeArgs with
        | [], [] -> instantiatedType
        | _ ->
            unifyApplications env name vs typeArgs
            instantiatedType

    let reportErrorIfHasTypeArgs env name = function
        | [] -> ()
        | ts -> reportArityMismatch env name 0 (List.length ts)

    let buildTypeOfDefinition env name d typeArgs =
        match d.typeKind with
        | TypeDefinitionKind.System c ->
            let types = CheckerEnv.types env
            match c with
            | SystemTypeCode.Boolean -> reportErrorIfHasTypeArgs env name typeArgs; types.boolean
            | SystemTypeCode.Nil -> reportErrorIfHasTypeArgs env name typeArgs; types.nil
            | SystemTypeCode.Number -> reportErrorIfHasTypeArgs env name typeArgs; types.number
            | SystemTypeCode.String -> reportErrorIfHasTypeArgs env name typeArgs; types.string
            | SystemTypeCode.Table -> systemTableType env name typeArgs
            | SystemTypeCode.Thread -> systemThreadType env name typeArgs
            |> Type.makeWithLocation (CheckerEnv.sourceLocation env (Name.measure name))

        | TypeDefinitionKind.Alias d
        | TypeDefinitionKind.Variable(_, d) ->
            if CheckerEnv.isMultiKind env d then
                // `M...<T>`
                let (Name { trivia = { span = nameSpan } }) = name
                CheckerEnv.reportError env nameSpan <| K.UnexpectedMultiType
                CheckerEnv.newValueVarType env CheckerEnv.TypeNames.lostByError
                |> Type.makeWithLocation (CheckerEnv.sourceLocation env nameSpan)
            else
                buildTypeOfAliasDefinition env name d typeArgs

    let splitLastVarOrReport (env: _ byref) ps = usingByrefAsRef &env (fun env ->
        let struct(psRev, v) =
            ps
            |> List.fold (fun struct(psRev, lastVar) { kind = D.Parameter(_, t) } ->
                match t.kind with
                | D.VariadicType v ->
                    match lastVar with
                    | Some lastVar -> CheckerEnv.reportError env.contents.env lastVar.trivia K.UnexpectedMultiType
                    | _ -> ()
                    psRev, Some v

                | _ -> t::psRev, lastVar
            ) ([], None)

        List.rev psRev, v
    )

    let rec typeSign (env: _ byref) t =
        let t' = typeSignOrMultiType &env t
        CheckerEnv.reportIfNotValueKind env.env t.trivia t'

    and functionParameters (env: _ byref) (D.Annotated(l, _), ps, D.Annotated(r, _)) =
        let ts, v =
            match ps with
            | None -> [], None
            | Some(D.Parameters ps) -> splitLastVarOrReport &env (SepBy.toList ps)

        parameters &env (Span.merge l.trivia r.trivia) (ts, v)

    and typeSignOrMultiType (env: _ byref) t =
        match t.kind with
        | D.WrappedType(_, t, _) -> typeSignOrMultiType &env t
        | D.NamedType(name, ts) -> namedType &env (name, ts)
        | D.ArrayType(et, _, _) -> arrayType &env t.trivia et
        | D.InterfaceType fs -> interfaceType &env t.trivia fs
        | D.FunctionType(_, l, m1, r, _, m2) -> functionType &env t.trivia (l, m1, r) m2
        | D.ConstrainedType(t, _, c) -> constrainedType &env t c

        | D.EmptyType _ -> parameters &env t.trivia ([], None)
        | D.SingleMultiType(_, { kind = D.Parameter(_, t) }, _, _) -> parameters &env t.trivia ([t], None)
        | D.VariadicType v -> parameters &env t.trivia ([], Some v)
        | D.MultiType2(p, _, D.Parameters ps) -> parameters &env t.trivia (splitLastVarOrReport &env (p::SepBy.toList ps))

    and parameters (env: _ byref) span (ts, v) = usingByrefAsRef &env (fun env ->
        let last = varParam &env.contents span v
        List.foldBack (fun t m ->
            let t' = typeSign &env.contents t
            let l = CheckerEnv.sourceLocation env.contents.env t.trivia
            CheckerEnv.types(env.contents.env).cons(t', m) |> Type.makeWithLocation l
        ) ts last
        )

    and collectTypeArgs' (env: _ byref) acc = function
        | [] -> List.rev acc
        | (_, t)::ts ->
            let t' = typeSignOrMultiType &env t
            collectTypeArgs' &env (struct(t', t.trivia)::acc) ts

    and collectTypeArgs (env: _ byref) = function
        | None -> []
        | Some(D.GenericArguments(_, SepBy(t, ts), _, _)) ->
            let t' = typeSignOrMultiType &env t
            collectTypeArgs' &env [struct(t', t.trivia)] ts

    and namedType (env: _ byref) (D.Annotated(Name n as name, _), ts) =
        let nameSpan = n.trivia.span
        match CheckerEnv.resolveType nameSpan n.kind env.env, n.kind, env.env.rare.selfType with
        | ValueSome d, _, _
        | ValueNone, "self", ValueSome d ->

            // 型名を発見した
            let ts = collectTypeArgs &env ts
            buildTypeOfDefinition env.env name d ts

        | _ ->

        // 型名が見つからなかった
        match n.kind, ts with

        // 空型として扱う
        | "void", None ->
            CheckerEnv.types(env.env).empty |> Type.makeWithLocation (CheckerEnv.sourceLocation env.env nameSpan)

        // それぞれ違う型変数として扱う
        // table<any,any> => table<?a,?b>
        | ("_" | "any"), None ->
            CheckerEnv.newValueVarType env.env n.kind
            |> Type.makeWithLocation (CheckerEnv.sourceLocation env.env nameSpan)

        // 同じ名前は同じ型変数として扱う
        // table<T,T> => table<?a,?a>
        | TypeVarLikeName true, None ->
            typeNameAsTypeVar &env name

        // 型名が見つからないエラーを報告
        | _ ->
            CheckerEnv.reportError env.env n.trivia.span (K.TypeNameNotFound n.kind)
            CheckerEnv.newValueVarType env.env CheckerEnv.TypeNames.lostByError
            |> Type.makeWithLocation (CheckerEnv.sourceLocation env.env nameSpan)

    and arrayType (env: _ byref) span elementType =
        let elementType = typeSign &env elementType
        let types = CheckerEnv.types env.env
        let l = CheckerEnv.sourceLocation env.env span

        types.table(types.number |> Type.makeWithLocation l, elementType)
        |> Type.makeWithLocation l

    and interfaceType (env: _ byref) span fs =
        let keyToType = fields &env fs
        InterfaceType keyToType |> Type.makeWithLocation (CheckerEnv.sourceLocation env.env span)

    and fields (env: _ byref) { kind = D.Fields(_, fs, _, _) } = usingByrefAsRef &env (fun env ->
        fs
        |> SepBy.fold (fun keyToType { kind = D.Field({ kind = k; trivia = ks }, _, t) } ->
            let t = typeSign &env.contents t

            match Map.tryFind k keyToType with
            | ValueSome struct(_, otherSpan) ->
                CheckerEnv.reportInfo env.contents.env ks <| K.DuplicateFieldKey(k, otherSpan)
            | _ -> ()

            Map.add k (t, ks) keyToType
        ) Map.empty
        |> Map.map (fun _ struct(t, _) -> t)
        )

    and functionType (env: _ inref) span (l, m1, r) m2 =
        let mutable env = { env with implicitVariadicParameterType = None }
        let m1 = functionParameters &env (l, m1, r)
        let types = CheckerEnv.types env.env
        let m2 = typeSignOrMultiType &env m2
        let m2 =
            if CheckerEnv.isMultiKind env.env m2 then m2 else
            types.cons(m2, types.empty |> Type.makeWithLocation m2.trivia)
            |> Type.makeWithLocation m2.trivia

        types.fn(m1, m2)
        |> Type.makeWithLocation (CheckerEnv.sourceLocation env.env span)

    and varParam (env: _ byref) span v =
        let { system = types } as typeEnv = CheckerEnv.typeEnv env.env
        match v with
        | None -> types.empty |> Type.makeWithLocation (CheckerEnv.sourceLocation env.env span)
        | Some { kind = D.VariadicTypeSign(n, _, c); trivia = span } ->

        let m = resolveMultiVar &env span n

        match c with
        | None -> ()
        | Some c ->
            let l = CheckerEnv.sourceLocation env.env c.trivia
            let c' = typeSign &env c |> MultiElementTypeConstraint |> Constraints.makeWithLocation l
            let n =
                match n with
                | Some(D.Annotated(Name n, _)) -> n.kind
                | _ -> CheckerEnv.TypeNames.implicitMultiVar

            let m' = CheckerEnv.newMultiVarTypeWith env.env n c' |> Type.makeWithLocation l
            match Type.unify typeEnv m m' with
            | ValueSome e -> CheckerEnv.reportError env.env c.trivia <| K.UnifyError e
            | _ -> ()
        m

    and constrainedType (env: _ byref) t c =
        let t' = typeSign &env t
        let fs = fields &env c
        let l = CheckerEnv.sourceLocation env.env c.trivia
        let c' = Constraints.ofInterfaceType fs |> Constraints.makeWithLocation l
        let ct = CheckerEnv.newValueVarTypeWith env.env CheckerEnv.TypeNames.constrainedType c' |> Type.makeWithLocation l
        CheckerEnv.reportIfUnifyError env.env t.trivia t' ct
        t'

    let ofTypeSign env t =
        let mutable env = {
            TypeResolveEnv.env = env
            implicitVariadicParameterType = None
        }
        typeSign &env t

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Constraints =
    let ofConstraintSign env x =
        let mutable env = {
            TypeResolveEnv.env = env
            implicitVariadicParameterType = None
        }
        Constraints.ofInterfaceType <| Type.fields &env x
