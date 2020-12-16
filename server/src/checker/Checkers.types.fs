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
    | RedeclarationOfSpecialGlobalVariable of name: string * oldKind: DeclarationKind * newKind: DeclarationKind
    | RedeclarationOfBasicType of SystemTypeCode
    | RedeclarationOfTypeVariable of name: string * oldTypeLocations: Location list
    | UndeterminedGlobalVariableEnvironment of modulePath: DocumentPath * additionalGlobals: Map<string, NonEmptyList<Declaration>>
    | GlobalNameCollision of name: string * decl1: Declaration * decl2: Declaration * decls: Declaration list
    | GlobalTypeCollision of name: string * type1: TypeDefinition * type2: TypeDefinition * types: TypeDefinition list
    | UnrecognizedFeatureName of featureName: string
    | UnexpectedMultiType
    | RequireMultiType
    | DuplicateTag of otherTag: Syntax.Documents.Tag
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

    let extend location n t env = { env with nameToDeclaration = Map.add n { scheme = t; declarationKind = DeclarationKind.NoFeatures; location = location } env.nameToDeclaration }

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
        | Some(Name({ kind = name; trivia = { span = nameSpan } })) ->

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

    let rec typeSign (env: _ byref) t =
        let t' = typeSignOrMultiType &env t
        CheckerEnv.reportIfNotValueKind env.env t.trivia t'

    and multiType (env: _ byref) t =
        let t' = typeSignOrMultiType &env t
        CheckerEnv.reportIfNotMultiKind env.env t.trivia t'

    and typeSignOrMultiType (env: _ byref) t =
        match t.kind with
        | D.NamedType(name, ts) -> namedType &env (name, ts)
        | D.ArrayType et -> arrayType &env t.trivia et
        | D.InterfaceType fs -> interfaceType &env t.trivia fs
        | D.FunctionType(m1, m2) -> functionType &env t.trivia m1 m2
        | D.ConstrainedType(t, c) -> constrainedType &env t c
        | D.MultiType(ps, v) -> parameters &env t.trivia (ps, v)

    and parameters (env: _ byref) span (ts, v) = usingByrefAsRef &env (fun env ->
        let last = varParam &env.contents span v
        List.foldBack (fun { kind = D.Parameter(_, t); trivia = s } m ->
            let t = typeSign &env.contents t
            let l = CheckerEnv.sourceLocation env.contents.env s
            CheckerEnv.types(env.contents.env).cons(t, m) |> Type.makeWithLocation l
        ) ts last
        )

    and collectTypeArgs (env: _ byref) acc = function
        | [] -> List.rev acc
        | t::ts ->
            let t' = typeSignOrMultiType &env t
            collectTypeArgs &env (struct(t', t.trivia)::acc) ts

    and namedType (env: _ byref) (Name n as name, ts) =
        let nameSpan = n.trivia.span
        match CheckerEnv.resolveType nameSpan n.kind env.env, n.kind, env.env.rare.selfType with
        | ValueSome d, _, _
        | ValueNone, "self", ValueSome d ->

            // 型名を発見した
            let ts = collectTypeArgs &env [] ts
            buildTypeOfDefinition env.env name d ts

        | _ ->

        // 型名が見つからなかった
        match n.kind, ts with

        // 空型として扱う
        | "void", [] ->
            CheckerEnv.types(env.env).empty |> Type.makeWithLocation (CheckerEnv.sourceLocation env.env nameSpan)

        // それぞれ違う型変数として扱う
        // table<any,any> => table<?a,?b>
        | ("_" | "any"), [] ->
            CheckerEnv.newValueVarType env.env n.kind
            |> Type.makeWithLocation (CheckerEnv.sourceLocation env.env nameSpan)

        // 同じ名前は同じ型変数として扱う
        // table<T,T> => table<?a,?a>
        | TypeVarLikeName true, [] ->
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

    and fields (env: _ byref) { kind = D.Fields fs } = usingByrefAsRef &env (fun env ->
        fs
        |> NonEmptyList.fold (fun keyToType { kind = D.Field({ kind = k; trivia = ks }, t) } ->
            let t = typeSign &env.contents t

            match Map.tryFind k keyToType with
            | ValueSome struct(_, otherSpan) ->
                CheckerEnv.reportInfo env.contents.env ks <| K.DuplicateFieldKey(k, otherSpan)
            | _ -> ()

            Map.add k (t, ks) keyToType
        ) Map.empty
        |> Map.map (fun _ struct(t, _) -> t)
        )

    and functionType (env: _ inref) span m1 m2 =
        let mutable env = { env with implicitVariadicParameterType = None }
        let m1 = multiType &env m1
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
        | Some { kind = D.VariadicParameter(n, c); trivia = span } ->

        let m = resolveMultiVar &env span n

        match c with
        | None -> ()
        | Some c ->
            let l = CheckerEnv.sourceLocation env.env c.trivia
            let c' = typeSign &env c |> MultiElementTypeConstraint |> Constraints.makeWithLocation l
            let n =
                match n with
                | Some(Name n) -> n.kind
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

module private DocumentCheckersHelpers =
    let reportParseErrors env span es =
        for e in es do
            CheckerEnv.reportInfo env span <| DiagnosticKind.ParseError e

module DocumentCheckers =
    open CheckerEnv
    open LuaChecker.Syntax
    open DocumentCheckersHelpers
    module D = Documents

    let featureNameToKind = function
        | "require" -> DeclarationKind.GlobalRequire |> ValueSome
        | "package" -> DeclarationKind.GlobalPackage |> ValueSome
        | _ -> ValueNone

    let inline parseFeatureOfTags (|Parse|) env tags =
        match tags with
        | [] -> ValueNone
        | _ ->

        tags
        |> List.fold (fun nearestKind tag ->
            match tag.kind with
            | D.FeatureTag(Name({ kind = Parse k as featureName } as name)) ->
                match nearestKind, k with
                | ValueNone, ValueSome k -> ValueSome struct(tag, k)
                | _, ValueNone ->
                    reportInfo env name.trivia.span <| DiagnosticKind.UnrecognizedFeatureName featureName
                    nearestKind

                | ValueSome struct(nearestTag, _), ValueSome _ ->
                    reportInfo env tag.trivia <| DiagnosticKind.DuplicateTag nearestTag
                    nearestKind
            | _ -> nearestKind
        ) ValueNone
        |> ValueOption.map (fun struct(_, k) -> k)

    let declKindOfModifierTags env modifierTags =
        parseFeatureOfTags featureNameToKind env modifierTags |> ValueOption.defaultValue DeclarationKind.NoFeatures

    let reportIfIncludesFeatureTag env modifierTags =
        parseFeatureOfTags (fun _ -> ValueNone) env modifierTags |> ValueOption.defaultValue ()

    let unifyDeclAndReport env (Name({ kind = n; trivia = { span = nameSpan } } )) typeSign newDecl oldDecl =

        // `require` や `package` などは警告付きで再宣言可能
        if oldDecl.declarationKind <> newDecl.declarationKind then
            let k = DiagnosticKind.RedeclarationOfSpecialGlobalVariable(n, oldDecl.declarationKind, newDecl.declarationKind)
            reportWarn env nameSpan k

        // 宣言済みの変数の型と一致しているか
        match Type.unify (typeEnv env) oldDecl.scheme newDecl.scheme with
        | ValueSome e -> reportError env typeSign.trivia (DiagnosticKind.UnifyError e); false
        | _ -> true

    let unifyTypeDeclAndReport env (Name({ trivia = { span = nameSpan } } )) newType oldDecl =
        match oldDecl.typeKind with

        // 基本型は再宣言できない
        | TypeDefinitionKind.System c ->
            let k = DiagnosticKind.RedeclarationOfBasicType c
            reportError env nameSpan k
            false

        | TypeDefinitionKind.Alias oldType ->

            // 宣言済みの変数の型と一致しているか
            match Type.unify (typeEnv env) oldType newType with
            | ValueSome e -> reportError env nameSpan (DiagnosticKind.UnifyError e); false
            | _ -> true

        // 型変数と同名の型は宣言できない
        // NOTE: このパターンに一致する構文は存在しない?
        | TypeDefinitionKind.Variable(name, _) ->
            let k = DiagnosticKind.RedeclarationOfTypeVariable(name, oldDecl.locations)
            reportError env nameSpan k
            false

    let unifyTypeDecls env name newType oldDecls = NonEmptyList.forall (unifyTypeDeclAndReport env name newType) oldDecls
    let unifyDecls env name typeSign newType oldDecls = NonEmptyList.forall (unifyDeclAndReport env name typeSign newType) oldDecls

    type TypeParameterBinding = {
        nameTokens: D.Name NonEmptyList
        varType: Type
        constraints: Choice<D.TypeConstraints, D.TypeSign> list
    }
    let consOption c cs = match c with None -> cs | Some c -> c::cs
    let collectTypeParameterBindsCore env kind nameToBind (Name { kind = name; trivia = nameTrivia } as nameToken, c) =
        let bind =
            match Map.tryFind name nameToBind with
            | ValueNone ->
                {
                    nameTokens = NonEmptyList.singleton nameToken

                    // 相互参照される制約を持つ型引数に対応するため、まず型制約なしで型変数を作る
                    // 後で制約付き型変数と型制約なしで型変数を単一化する
                    varType = newVarType env name kind |> Type.makeWithLocation (sourceLocation env nameTrivia.span)

                    constraints = Option.toList c
                }
            | ValueSome bind ->

                // 型変数の種を単一化する
                // @generic T
                // @generic T...
                match unifyKind (Type.kind (typeEnv env) bind.varType) kind with
                | ValueSome e ->
                    let (Name n) = nameToken
                    reportError env n.trivia.span <| DiagnosticKind.UnifyError e

                | _ -> ()

                {
                    nameTokens = NonEmptyList.append bind.nameTokens (NonEmptyList.singleton nameToken)
                    varType = bind.varType
                    constraints = consOption c bind.constraints
                }

        Map.add name bind nameToBind

    let foldTypeParameters folder state tags =
        tags
        |> List.fold (fun s tag ->
            match tag.kind with
            | D.GenericTag ps -> NonEmptyList.fold folder s ps
            | _ -> s
        ) state

    let collectEmptyBinds (Types types as env) map tags =
        tags
        |> foldTypeParameters (fun map p ->
            match p.kind with
            | D.TypeParameter(name, c) -> collectTypeParameterBindsCore env types.valueKind map (name, Option.map Choice1Of2 c)
            | D.VariadicTypeParameter(name, c) -> collectTypeParameterBindsCore env types.multiKind map (name, Option.map Choice2Of2 c)
        ) map

    let extendTypeEnvFromBind nameToBind env =
        nameToBind
        |> Map.fold (fun env n bind ->
            let locations = bind.nameTokens |> NonEmptyList.toList |> List.map (fun (Name n) -> Location(env.rare.noUpdate.filePath, n.trivia.span))
            let kind = TypeDefinitionKind.Variable(n, bind.varType)
            let definition = {
                locations = locations
                typeKind = kind
            }
            extendType n definition env
        ) env

    let extendTypeEnvFromGenericTags modifierTags env =
        match modifierTags with
        | [] -> env
        | _ ->

        // まず制約なしの型変数を作る ( 相互参照される型に対応するため )
        //
        // `type p: { x: n }, p: { y: n }, n. …` の場合
        // nameToBind = `Map ["p", (?p, ["{ x: n }"; "{ y: n }"]`); "n", (?n, [])]`
        let nameToBind = collectEmptyBinds env Map.empty <| List.rev modifierTags

        // 型引数注釈がなかったので終わり
        if Map.isEmpty nameToBind then env else

        // 制約なしの型変数で型環境を拡張する
        // typeEnv = typeEnv @ ["p", ?p'; "n", ?n']
        let env = extendTypeEnvFromBind nameToBind env

        // 制約なしの型変数と一時的に作った型制約付き型変数を単一化する
        //
        // unify ?p (?p': { x: ?n })
        // unify ?p (?p'': { y: ?n })
        for kv in nameToBind do
            let bind = kv.Value
            let (Name { kind = varName }) = bind.nameTokens |> NonEmptyList.head
            for c in bind.constraints do
                let span =
                    match c with
                    | Choice1Of2 c -> c.trivia
                    | Choice2Of2 e -> e.trivia

                let v' =
                    match c with
                    | Choice1Of2 c ->
                        let l = sourceLocation env c.trivia
                        let c' = Constraints.ofConstraintSign env c |> Constraints.makeWithLocation l
                        newValueVarTypeWith env varName c' |> Type.makeWithLocation l

                    | Choice2Of2 e ->
                        let l = sourceLocation env e.trivia
                        let c = Type.ofTypeSign env e |> MultiElementTypeConstraint |> Constraints.makeWithLocation l
                        newMultiVarTypeWith env varName c |> Type.makeWithLocation l

                reportIfUnifyError env span bind.varType v'
        env

    let findTypeTag env span struct(ds, es) =
        reportParseErrors env span es

        let mutable modifierTags = []
        let mutable lastTypeTag = ValueNone
        for { kind = D.Document(_, tags) } in ds do
            for tag in tags do
                match tag.kind with
                | D.TypeTag t ->
                    match lastTypeTag with
                    | ValueSome struct(_, span, _) -> reportInfo env span <| DiagnosticKind.DuplicateTag tag
                    | _ -> ()
                    lastTypeTag <- ValueSome(modifierTags, tag.trivia, t)
                    modifierTags <- []

                | _ -> modifierTags <- tag::modifierTags

        match lastTypeTag with
        | ValueNone -> ValueNone
        | ValueSome(modifierTags, _, typeSign) ->
            let env' = enterTypeScope env
            let env' = extendTypeEnvFromGenericTags modifierTags env'
            let t = Type.ofTypeSign env' typeSign
            let t = Scheme.generalize env.rare.typeLevel t
            ValueSome struct(typeSign, t)

    let globalTag env modifierTags (Name({ kind = n; trivia = { span = nameSpan } }) as name, typeSign) =
        let kind = declKindOfModifierTags env modifierTags
        let env' = enterTypeScope env
        let env' = enterTemporaryTypeVarNameScope env'
        let env' = extendTypeEnvFromGenericTags modifierTags env'

        // グローバル変数宣言の型変数スコープはそのタグのみ
        let t = Type.ofTypeSign env' typeSign
        let t = Scheme.generalize 0 t

        let l = Some <| Location(env.rare.noUpdate.filePath, nameSpan)
        let d = { declarationKind = kind; scheme = t; location = l }
        let g = env.rare.noUpdate.additionalGlobalEnv

        let d =
            match Map.tryFind n g.Value.names with
            | ValueSome(NonEmptyList(_, ds') as dds') ->
                if unifyDecls env name typeSign d dds'
                then NonEmptyList(d, ds')
                else NonEmptyList.cons d dds'
            | _ ->

            match Map.tryFind n env.rare.noUpdate.defaultGlobalEnv.names with
            | ValueSome dds' -> unifyDecls env name typeSign d dds' |> ignore
            | _ -> ()

            NonEmptyList.singleton d

        g.Value <- { g.Value with names = Map.add n d g.Value.names }

    type BuildingType<'typeName,'tempType,'fields,'tempEnv> = {
        typeName: 'typeName
        tempType: 'tempType
        fields: 'fields
        tempEnv: 'tempEnv
        isStringMetaTableIndex: bool
    }
    let classTag env modifierTags (Name { kind = n; trivia = nameTrivia } as name, parent) =
        let isStringMetaTableIndex =
            parseFeatureOfTags (function "stringMetaTableIndex" -> ValueSome true | _ -> ValueNone) env modifierTags
            |> ValueOption.defaultValue false

        // 自動型変数のためのスコープの開始
        let env = enterTemporaryTypeVarNameScope env
        let env = enterTypeScope env

        let env = extendTypeEnvFromGenericTags modifierTags env
        let t = newValueVarType env n |> Type.makeWithLocation (sourceLocation env nameTrivia.span)
        let d = {
            locations = [Location(env.rare.noUpdate.filePath, Name.measure name)]
            typeKind = TypeDefinitionKind.Alias t
        }
        let env = extendType n d env

        // self として登録
        let env = { env with rare = { env.rare with selfType = ValueSome d } }

        match parent with
        | None -> ()
        | Some p ->
            let parentName =
                match p.kind with
                | D.NamedType(Name { kind = k }, _) -> k
                | _ -> TypeNames.classParent

            let p' = Type.ofTypeSign env p

            // 親がインターフェース型ならインターフェース制約とみなす
            let p' =
                match p'.kind with
                | InterfaceType fs ->
                    let l = sourceLocation env p.trivia
                    let c = Constraints.ofInterfaceType fs |> Constraints.makeWithLocation l
                    newValueVarTypeWith env parentName c |> Type.makeWithLocation l

                | _ -> p'

            reportIfUnifyError env (Name.measure name) t p'

        {
            typeName = name
            tempType = t
            fields = Map.empty
            tempEnv = env
            isStringMetaTableIndex = isStringMetaTableIndex
        }

    let fieldTag env modifierTags lastClass tagSpan (visibility, key, typeSign) =
        match lastClass with
        | ValueNone -> reportInfo env tagSpan DiagnosticKind.FieldParentTagNotFound; ValueNone
        | ValueSome({ tempEnv = tempEnv } as lastClass) ->

        reportIfIncludesFeatureTag tempEnv modifierTags

        // TODO: 現在 visibility は警告なしに無視されている
        let _ = visibility

        // 重複したキーをもつフィールドが存在していても問題はない ( 型の不一致エラーは出る ) が
        // ユーザーへの情報提供のため、ここでチェックする
        match Map.tryFind key.kind lastClass.fields with
        | ValueSome otherSpan -> reportInfo tempEnv key.trivia <| DiagnosticKind.DuplicateFieldKey(key.kind, otherSpan)
        | _ -> ()

        let fieldType =
            let tempEnv = enterTypeScope tempEnv
            let tempEnv = extendTypeEnvFromGenericTags modifierTags tempEnv
            Type.ofTypeSign tempEnv typeSign

        // フィールドに @generic で明示的に指定された型変数だけが汎用化される
        let fieldType = Scheme.generalize tempEnv.rare.typeLevel fieldType

        // 現在交差型はないので、
        // 変換中の型は、もしインターフェース型ならインターフェース制約付き型変数に変換する
        // フィールドのキーと型は、1要素のインターフェース型制約付き型変数に変換する
        // そして型変数同士を単一化する
        //
        // 変換中の型: `{ x: number }`
        // フィールドのキー: `y`
        // フィールドの型: `number`
        // として
        // `{ x: number } & { y: number }` の代わりに
        // 変換中の型 `{ x: number }` を `?a: { x: number }` に変換し
        // `unify (?a: { x: number }) (?b: { y: number })` を行い
        // 変換中の型が `?a: { x: number, y: number }` になる
        let tempType = lastClass.tempType

        /// `{ key: fieldType }`
        let keyValueType =
            let keyValueName = TypeNames.fromFieldKey key.kind |> ValueOption.defaultValue TypeNames.fieldKeyValueInterface
            let fs = Map.add key.kind fieldType Map.empty
            let l = sourceLocation env tagSpan
            let c = Constraints.ofInterfaceType fs |> Constraints.makeWithLocation l
            newValueVarTypeWith tempEnv keyValueName c |> Type.makeWithLocation l

        // ここで
        // 親型との不一致 `---@class X : number @field f1 string` や
        // フィールド型の不一致 `---@class Y : { f1: number } @field f1 string`
        // などが報告される
        reportIfUnifyError tempEnv typeSign.trivia tempType keyValueType

        ValueSome {
            typeName = lastClass.typeName
            tempType = tempType
            fields = Map.add key.kind key.trivia lastClass.fields
            tempEnv = tempEnv
            isStringMetaTableIndex = lastClass.isStringMetaTableIndex
        }

    /// `type … (a: C) … . a` で C がインターフェース制約で C の中に a がないとき、`type … . C` に変換する
    let interfaceConstraintToInterfaceType env nameSpan t =
        let struct(_, t') = Scheme.instantiate 1 t
        match t'.kind with
        | VarType({ target = LuaChecker.Var(_, ({ kind = InterfaceConstraint fs } as c)) } as r) when Constraints.hasField c ->
            let varsEnv = {
                visitedVars = []
                other = { level = 0 }
            }
            let vs = Constraints.freeVars' varsEnv [] c
            match Assoc.tryFindBy VarType.physicalEquality r vs with
            | ValueNone -> InterfaceType fs |> Type.makeWithLocation (sourceLocation env nameSpan) |> Scheme.generalize 0
            | _ -> t
        | _ -> t

    let endClass lastClass =
        let Name({ kind = n } as nameToken) as name = lastClass.typeName
        let tempType = lastClass.tempType
        let env = lastClass.tempEnv

        // 自由変数はここで型引数に変換される
        // `---@class Vec4 : Vec2<T> @field z T @field w T` は
        // `---@generic T @class Vec4 : Vec2<T> @field z T @field w T` と同じ
        let generalizedType = Scheme.generalize 0 tempType

        let generalizedType = interfaceConstraintToInterfaceType env nameToken.trivia.span generalizedType

        let g = env.rare.noUpdate.additionalGlobalEnv

        let d = {
            typeKind = TypeDefinitionKind.Alias generalizedType
            locations = [Location(env.rare.noUpdate.filePath, nameToken.trivia.span)]
        }
        let d =
            match Map.tryFind n g.Value.types with
            | ValueSome(NonEmptyList(_, ds') as dds') ->
                if unifyTypeDecls env name generalizedType dds'
                then NonEmptyList(d, ds')
                else NonEmptyList.cons d dds'
            | _ ->

            match Map.tryFind n env.rare.noUpdate.defaultGlobalEnv.types with
            | ValueSome dds' -> unifyTypeDecls env name generalizedType dds' |> ignore
            | _ -> ()

            NonEmptyList.singleton d

        g.Value <- { g.Value with types = Map.add n d g.Value.types }

        // 文字列の追加インターフェースを表す型を追加する
        if lastClass.isStringMetaTableIndex then
            g
            |> Local.modify (fun g ->
                { g with stringMetaTableIndexType = g.stringMetaTableIndexType @ [generalizedType] }
            )

    let processRemainingModifierTags env modifierTags =
        for tag in modifierTags do
            match tag.kind with

            // 親構文への注釈
            | D.FeatureTag(Name { kind = featureName } as name) ->
                reportInfo env (Name.measure name) <| DiagnosticKind.UnrecognizedFeatureName featureName

            | D.GenericTag _ ->
                reportInfo env tag.trivia DiagnosticKind.GenericTagParentSyntaxNotFound

            // TODO: 親構文を修飾する @type を実装する
            | D.TypeTag _ ->
                reportInfo env tag.trivia DiagnosticKind.TypeTagParentSyntaxNotFound

            | D.ClassTag _
            | D.FieldTag _
            | D.GlobalTag _
            | D.UnknownTag _
                -> ()

    let statementLevelTags env span struct(ds, es) =
        reportParseErrors env span es

        let mutable modifierTags = []
        let mutable lastClass = ValueNone
        for { kind = D.Document(_, tags) } in ds do
            for tag in tags do
                match tag.kind with
                | D.GlobalTag(name, typeSign) ->
                    ValueOption.iter endClass lastClass
                    lastClass <- ValueNone
                    globalTag env modifierTags (name, typeSign)
                    modifierTags <- []

                | D.ClassTag(name, parent) ->
                    ValueOption.iter endClass lastClass
                    lastClass <- ValueSome <| classTag env modifierTags (name, parent)
                    modifierTags <- []

                | D.FieldTag(visibility, name, typeSign) ->
                    lastClass <- fieldTag env modifierTags lastClass tag.trivia (visibility, name, typeSign)
                    modifierTags <- []

                | _ -> modifierTags <- tag::modifierTags

        ValueOption.iter endClass lastClass
        lastClass <- ValueNone
        processRemainingModifierTags env modifierTags
