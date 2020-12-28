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
    | DuplicateTag of otherTagName: string * otherTagSpan: Span
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
