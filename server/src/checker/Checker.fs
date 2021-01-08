module LuaChecker.Checker
open LuaChecker.Primitives
open LuaChecker.TypeSystem
open System.Collections.Concurrent


let standardTypeSystem =
    let valueKind = NamedKind "value"
    let multiKind = NamedKind "multi"
    let booleanConstant = TypeConstant("boolean", valueKind)
    let numberConstant = TypeConstant("number", valueKind)
    let stringConstant = TypeConstant("string", valueKind)
    let valueType0 c = NamedType(c, [])
    let emptyConstant = TypeConstant("()", multiKind)
    let tableConstant = TypeConstant("table", FunKind([valueKind; valueKind], valueKind))
    let threadConstant = TypeConstant("thread", FunKind([multiKind; multiKind], valueKind))
    let consConstant = TypeConstant("(::)", FunKind([valueKind; multiKind], multiKind))
    let funConstant = TypeConstant("(fun)", FunKind([multiKind; multiKind], valueKind))

    let literalNaming = function
        | Syntaxes.Nil -> "nil"
        | Syntaxes.False -> "false"
        | Syntaxes.True -> "true"
        | Syntaxes.Number _ -> "n"
        | Syntaxes.String x -> x

    /// type(x: tag..): x
    let tagOrUpperConstraint lowerBound = UnionConstraint(lowerBound = lowerBound, upperBound = UniversalTypeSet)

    /// e.g. `type(x: 10..): x`
    let makeLiteral x = fun location ->
        LiteralType x
        |> Type.makeWithLocation location
        |> List.singleton
        |> TypeSet
        |> tagOrUpperConstraint
        |> Constraints.makeWithLocation location
        |> Type.newVarWith (literalNaming x) 1000000 valueKind
        |> Type.makeWithLocation location

    let literalCacheMaxCount = 256
    let literalCache = ConcurrentDictionary<_,_>()
    let makeLiteralFunc = System.Func<_,_> makeLiteral

    let literalCache0 =
        seq {
            Syntaxes.Nil
            Syntaxes.False
            Syntaxes.True
            for x in -10. .. 1. .. 10. do
                Syntaxes.Number x

            Syntaxes.String ""
            for c in 0 .. 128 do
                Syntaxes.String <| string (char c)
        }
        |> Seq.fold (fun map x -> Map.add x (makeLiteral x) map) Map.empty

    /// type(a: x..): a
    let literal struct(x, location) =
        match Map.tryFind x literalCache0 with
        | ValueSome t -> t location
        | _ ->

        if literalCacheMaxCount < literalCache.Count then
            literalCache.Clear()
        literalCache.GetOrAdd(x, valueFactory = makeLiteralFunc) location
    {
        nil = LiteralType Syntaxes.Nil
        booleanConstant = booleanConstant
        boolean = valueType0 booleanConstant
        numberConstant = numberConstant
        number = valueType0 numberConstant
        stringConstant = stringConstant
        string = valueType0 stringConstant
        literal = literal

        tableConstant = tableConstant
        table = fun struct(k, v) -> NamedType(tableConstant, [k; v])
        unTable = function NamedType(t, [k; v]) when t = tableConstant -> ValueSome(k, v) | _ -> ValueNone
        threadConstant = threadConstant
        thread = fun struct(i, o) -> NamedType(threadConstant, [i; o])
        unThread = function NamedType(t, [i; o]) when t = threadConstant -> ValueSome(i, o) | _ -> ValueNone

        emptyConstant = emptyConstant
        empty = NamedType(emptyConstant, [])
        cons = fun struct(t, m) -> NamedType(consConstant, [t; m])
        unCons = function NamedType(t, [x; m]) when t = consConstant -> ValueSome(x, m) | _ -> ValueNone

        /// `fun(...): ...`
        fnConstant = funConstant
        fn = fun struct(p, r) -> NamedType(funConstant, [p; r])
        unFn = function NamedType(t, [p; r]) when t = funConstant -> ValueSome(p, r) | _ -> ValueNone

        valueKind = valueKind
        multiKind = multiKind
}
let private systemType code = { typeKind = TypeDefinitionKind.System code; locations = [] }
let standardTypes = Map [
    "nil", systemType SystemTypeCode.Nil
    "boolean", systemType SystemTypeCode.Boolean
    "number", systemType SystemTypeCode.Number
    "string", systemType SystemTypeCode.String
    "table", systemType SystemTypeCode.Table
    "thread", systemType SystemTypeCode.Thread
]
let standardEnv packagePath = {
    typeSystem = standardTypeSystem
    derivedTypes = TypeCache.create standardTypeSystem
    initialGlobalEnv = {
        names = Map.empty
        types = standardTypes |> Map.map (fun _ -> NonEmptyList.singleton)
        stringMetaTableIndexType = []
    }
    packagePath = packagePath
}
let updateDescendants file project =
    project.pathToSourceFile
    |> HashMap.fold (fun struct(project, descendants) sourcePath sourceFile ->
        match sourceFile.stage with
        | BeforeParse _ -> project, descendants
        | AnalysisComplete(s, _) ->
            if not <| Set.contains file s.typedTree.ancestorModulePaths then project, descendants else

            // sourceFile が file を参照していた
            let sourceFile = {
                stage = BeforeParse
                source = sourceFile.source
            }
            Project.addSourceFileNoCheck sourcePath sourceFile project, sourcePath::descendants

    ) (project, [])

let checkSourceCore project filePath source =
    let struct(syntaxTree, diagnostics) = Checkers.parse project.projectRare.fileSystem source
    Checkers.checkSyntaxAndCache project filePath source diagnostics syntaxTree

///<summary>(&lt;=)</summary>
let isOlder source1 source2 =
    match source1, source2 with
    | InMemory(_, v1), InMemory(_, v2) -> v1 <= v2
    | InFs(_, v1), InFs(_, v2) -> v1 <= v2
    | _ -> false

let parseAndCheckCached project filePath source =
    match Project.tryFind filePath project with
    | ValueSome sourceFile when isOlder source sourceFile.source ->
        let tree, e, project = Checkers.checkSourceFileCached project filePath sourceFile
        tree, e, project, []

    | _ ->
        let tree, e, project = checkSourceCore project filePath source
        let struct(project, descendants) = updateDescendants filePath project
        tree, e, project, descendants

let addOrUpdateSourceFile file project =
    let sourceFile = {
        stage = BeforeParse
        source = InFs(file, project.projectRare.fileSystem.lastWriteTime file)
    }
    let project = Project.addSourceFileNoCheck file sourceFile project
    updateDescendants file project

let removeSourceFile file project =
    let project = Project.remove file project
    updateDescendants file project

let isAncestor old young project =
    match Project.tryFind young project with
    | ValueSome { stage = AnalysisComplete(check, _) } -> Set.contains old check.typedTree.ancestorModulePaths
    | _ -> false

let addInitialGlobalModules project globalModulePaths =
    let project, globalEnv =
        globalModulePaths
        |> List.fold (fun (project, globalEnv) globalModulePath ->
            let lastWriteTime =
                try project.projectRare.fileSystem.lastWriteTime globalModulePath
                with _ -> System.DateTime.MinValue

            let chunk, _, project, _ = parseAndCheckCached project globalModulePath (InFs(globalModulePath, lastWriteTime))
            project, Env.merge NonEmptyList.append NonEmptyList.append globalEnv chunk.additionalGlobalEnv

        ) (project, project.projectRare.initialGlobal.initialGlobalEnv)

    { project with
        projectRare =
        { project.projectRare with
            initialGlobal =
            { project.projectRare.initialGlobal with
                initialGlobalEnv = globalEnv
            }
        }
    }
