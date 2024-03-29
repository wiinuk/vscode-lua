namespace LuaChecker.Checker.Test
open LuaChecker
open LuaChecker.Checker
open LuaChecker.Primitives
open LuaChecker.Syntaxes
open LuaChecker.TypeSystem
open System.IO
open System.Collections.Concurrent


module rec TypeExtensions =
    type K = LuaChecker.DiagnosticKind

    let types' = standardTypeSystem
    let typeEnv' = { system = types'; stringTableTypes = [] }
    let stringKeyInterfaceType fs = fs |> Seq.map (fun (k, t) -> FieldKey.String k, t) |> Map
    let withEmptyLocation x = { kind = x; trivia = [] }

    module Type =
        let empty = types'.empty |> Type.makeWithEmptyLocation
        let literalType v = LiteralType v |> Type.makeWithEmptyLocation
        let numberLiteralType n = n |> Number |> literalType
        let stringLiteralType n = n |> String |> literalType
        let interfaceType fs = stringKeyInterfaceType fs |> InterfaceType |> Type.makeWithEmptyLocation
        let newVarWithFields level fs = Type.newVarWith "" level types'.valueKind (Constraints.ofFields fs) |> Type.makeWithEmptyLocation
        let newValueVarWith level c = Type.newVarWith "" level types'.valueKind c |> Type.makeWithEmptyLocation
        let newMultiVarWith level c = Type.newVarWith "" level types'.multiKind c |> Type.makeWithEmptyLocation
        let newVar level = TypeSystem.Type.newVar "" level types'.valueKind |> Type.makeWithEmptyLocation
        let newAssigned t =
            let unusedLevel = 1
            let v = Var.newVar "" unusedLevel (Type.kind typeEnv' t)
            v.target <- Assigned t
            VarType v |> Type.makeWithEmptyLocation

    type NormalizeState = {
        mutable nextId: int64
        mutable ids: Map<TypeParameterId, TypeParameterId>
        mutable vs: VarTypeSite list
        mutable reduced: bool
    }
    let newEmptyState() = { nextId = 0L; ids = Map.empty; vs = []; reduced = false }
    let clearVisitedVarsAndMultiVars s = s.vs <- []

    let fleshId s kind =
        let x = TypeParameterId(s.nextId, kind)
        s.nextId <- s.nextId + 1L
        x

    module TypeParameterId =
        let kind (TypeParameterId(_, k)) = k

    let addIfFlesh id state =
        if Map.containsKey id state.ids then () else
        state.ids <- Map.add id (fleshId state <| TypeParameterId.kind id) state.ids

    let getNewId ({ ids = ids } as state) id =
        let id' = Map.find id ids
        if id <> id' then state.reduced <- true
        id'

    let addVar v state =
        if List.contains v state.vs then false else
        state.vs <- v::state.vs
        true

    module ParameterIdCollectors =
        let rec fields ids fs =
            for _, t in Map.toSeq fs do
                type' ids t

        and constraints ids c =
            match c.kind with
            | MultiElementTypeConstraint t -> type' ids t
            | InterfaceConstraint fs -> fields ids fs
            | UnionConstraint(l, u) ->
                for t in TypeSet.toList l do type' ids t
                for t in TypeSet.toList u do type' ids t

        and type' ids t =
            match t.kind with
            | ParameterType id -> addIfFlesh id ids
            | NamedType(_, ts) -> for t in ts do type' ids t
            | LiteralType _ -> ()
            | InterfaceType fs -> fields ids fs
            | VarType v ->
                if addVar v ids then
                    match v.target with
                    | Assigned t -> type' ids t
                    | LuaChecker.Var(_, c) -> constraints ids c

            | TypeAbstraction(ps, t) ->
                for TypeParameter(_, id, c) in ps do
                    addIfFlesh id ids
                    constraints ids c

                type' ids t

    module ParameterIdReplacers =
        let toReducer collector replacer x =
            let ids = newEmptyState()
            collector ids x
            clearVisitedVarsAndMultiVars ids
            ids.reduced <- false
            let x = replacer ids x
            if ids.reduced
            then ValueSome x
            else ValueNone

        let rec type' ids t =
            match t.kind with
            | ParameterType id -> getNewId ids id |> ParameterType |> Type.withEntity t
            | NamedType(n, ts) -> NamedType(n, List.map (type' ids) ts) |> Type.withEntity t
            | LiteralType _ -> t
            | InterfaceType fs -> fields ids fs |> InterfaceType |> Type.withEntity t
            | VarType r ->
                if addVar r ids then
                    match r.target with
                    | Assigned t ->
                        ids.reduced <- true
                        type' ids t

                    | LuaChecker.Var(l, c) ->
                        let c = constraints ids c
                        r.target <- LuaChecker.Var(l, c)
                        t
                else
                    t

            | TypeAbstraction([], t) ->
                ids.reduced <- true
                t

            | TypeAbstraction(ps, t) ->
                let ps = [
                    for TypeParameter(n, id, c) in ps do
                        TypeParameter(n, getNewId ids id, constraints ids c)
                ]
                let t = type' ids t
                TypeAbstraction(ps, t) |> Type.withEntity t

        and constraints ids c =
            match c.kind with
            | InterfaceConstraint fs -> fields ids fs |> InterfaceConstraint |> Constraints.withEntity c
            | MultiElementTypeConstraint t -> type' ids t |> MultiElementTypeConstraint |> Constraints.withEntity c
            | UnionConstraint(l, u) -> UnionConstraint(TypeSet.map (type' ids) l, TypeSet.map (type' ids) u) |> Constraints.withEntity c

        and fields ids fs = Map.map (fun _ -> type' ids) fs

    type SimplifierEnv<'pts,'visited,'reduced> = {
        pts: 'pts
        visited: 'visited
        reduced: 'reduced
    }

    module ConstraintSimplifiers =
        let trySimpleConstraint' = function
            | MultiElementTypeConstraint e ->
                match e with
                | { kind = LiteralType Nil } ->
                    // ...nil => ()
                    ValueSome types'.empty
                | _ -> ValueNone

            | UnionConstraint(lower, upper) ->
                let (<=..) t1 t2 = TypeSet.isSubset types' t1 t2 |> Result.defaultValue false
                let (=.) t1 t2 = let t = TypeSet [withEmptyLocation t2] in t1 <=.. t && t <=.. t1
                let (<=.) t1 t2 = t1 <=.. TypeSet [withEmptyLocation t2]

                if TypeSet.isUniversal upper then

                    // x.. (x <= nil) => nil
                    // x.. (x <= boolean) => boolean
                    // x.. (x <= number) => number
                    // x.. (x <= string) => string
                    if lower <=. types'.nil then
                        ValueSome types'.nil
                    elif lower <=. types'.boolean then
                        ValueSome types'.boolean
                    elif lower <=. types'.number then
                        ValueSome types'.number
                    elif lower <=. types'.string then
                        ValueSome types'.string

                    else
                        ValueNone
                else

                // l..nil
                // l..boolean
                // l..number
                // l..string
                if upper =. types'.nil then
                    ValueSome types'.nil
                elif upper =. types'.boolean then
                    ValueSome types'.boolean
                elif upper =. types'.number then
                    ValueSome types'.number
                elif upper =. types'.string then
                    ValueSome types'.string

                else
                    ValueNone

            | _ -> ValueNone

        let trySimpleConstraint c =
            trySimpleConstraint' c.kind
            |> ValueOption.map (fun t -> { kind = t; trivia = c.trivia })

        let constraints env c =
            match c.kind with
            | InterfaceConstraint fs -> fs |> Map.map (fun _ -> type' env) |> InterfaceConstraint |> Constraints.withEntity c
            | MultiElementTypeConstraint t -> type' env t |> MultiElementTypeConstraint |> Constraints.withEntity c
            | UnionConstraint(l, u) ->
                UnionConstraint(
                    TypeSet.map (type' env) l,
                    TypeSet.map (type' env) u
                )
                |> Constraints.withEntity c

        let type' env t =
            match t.kind with
            | NamedType(c, ts) -> NamedType(c, List.map (type' env) ts) |> Type.withEntity t
            | LiteralType _ -> t
            | InterfaceType fs -> fs |> Map.map (fun _ -> type' env) |> InterfaceType |> Type.withEntity t

            // simple (type('0: 10..): ('0, string)) = (number, string)
            | ParameterType p ->
                match Assoc.tryFind p env.pts with
                | ValueSome t -> t
                | _ -> t

            | TypeAbstraction(ps, et) ->
                let acc, env =
                    ps
                    |> List.fold (fun (acc, env) (TypeParameter(_, id, c) as p) ->
                        match trySimpleConstraint c with
                        | ValueSome t ->
                            env.reduced := true
                            acc, { env with pts = Assoc.add id t env.pts }

                        | _ -> p::acc, env

                    ) ([], env)

                let ps =
                    [ for TypeParameter(n, id, c) in List.rev acc do
                        TypeParameter(n, id, constraints env c)
                    ]

                TypeAbstraction(ps, type' env et) |> Type.withEntity t

            | VarType r ->
                match Assoc.tryFind r env.visited with
                | ValueSome() -> t
                | _ ->
                let env = { env with visited = Assoc.add r () env.visited }

                r.target <-
                    match r.target with
                    | Assigned t -> Assigned <| type' env t
                    | LuaChecker.Var(l, c) ->

                    match trySimpleConstraint c with
                    | ValueSome t ->
                        env.reduced := true
                        Assigned t

                    | _ -> LuaChecker.Var(l, constraints env c)
                t

        let toReducer simple x =
            let env = {
                visited = Assoc.empty
                pts = Assoc.empty
                reduced = ref false
            }
            let x = simple env x
            if !env.reduced
            then ValueSome x
            else ValueNone

    module Reducer =
        let noop _ = ValueNone
        let merge r1 r2 x =
            match r1 x with
            | ValueNone -> r2 x
            | ValueSome x as r ->

            match r2 x with
            | ValueNone -> r
            | r -> r

        let mergeMany rs = List.fold merge noop rs

        let repeat maxRepeat reducer x =
            if maxRepeat <= 0 then x else

            match reducer x with
            | ValueSome x -> repeat (maxRepeat - 1) reducer x
            | _ -> x

        let once reducer x = reducer x |> ValueOption.defaultValue x

    module TriviaSimplifiers =
        let toReducer simple x =
            let reduced = ref false
            let x = simple struct([], reduced) x
            if !reduced then ValueSome x else ValueNone

        let trivia struct(_, reduced) t f =
            if t.trivia <> [] then
                reduced := true

            withEmptyLocation <| f t.kind

        let type' env t = trivia env t <| function
            | NamedType(c, ts) -> NamedType(c, List.map (type' env) ts)
            | LiteralType _ as t -> t
            | InterfaceType fs -> InterfaceType <| Map.map (fun _ -> type' env) fs
            | ParameterType _ as t -> t
            | TypeAbstraction(ps, t) -> TypeAbstraction(List.map (typeParameter env) ps, type' env t)
            | VarType r as t ->
                let struct(vs, reduced) = env
                if List.contains r vs then t else
                let env = struct(r::vs, reduced)

                r.target <-
                    match r.target with
                    | Assigned t -> Assigned <| type' env t
                    | LuaChecker.Var(l, c) -> LuaChecker.Var(l, constraints env c)
                t

        let constraints env c = trivia env c <| function
            | InterfaceConstraint fs -> Map.map (fun _ -> type' env) fs |> InterfaceConstraint
            | MultiElementTypeConstraint t -> type' env t |> MultiElementTypeConstraint
            | UnionConstraint(l, u) ->
                UnionConstraint(
                    TypeSet.map (type' env) l,
                    TypeSet.map (type' env) u
                )

        let typeParameter (struct(_, reduced) as env) (TypeParameter(x, id, c)) =
            if x <> "" then reduced := true
            TypeParameter("", id, constraints env c)

    module Constraints =
        let withLocation l c = { c with trivia = l }
        let ofFields fs = fs |> stringKeyInterfaceType |> Constraints.ofInterfaceType |> Constraints.makeWithEmptyLocation
        let ofSpace(lowerBound, upperBound) = UnionConstraint(lowerBound = TypeSet lowerBound, upperBound = TypeSet upperBound) |> Constraints.makeWithEmptyLocation
        /// tag..
        let tagOrUpper lowerBound = UnionConstraint(TypeSet lowerBound, UniversalTypeSet) |> Constraints.makeWithEmptyLocation
        /// (lowerBound1 | lowerBound2 | …)..
        let literalsOrUpper lowerBounds =
            let lowerBounds =
                lowerBounds
                |> List.map (Type.literalType >> List.singleton)
                |> List.fold (fun ts1 ts2 -> TypeSet.union types' ts1 (TypeSet ts2) |> Result.defaultWith (failwithf "%A")) TypeSet.empty
            UnionConstraint(lowerBounds, UniversalTypeSet) |> Constraints.makeWithEmptyLocation
        /// x..
        let numberOrUpper lowerBound = lowerBound |> Number |> Type.literalType |> List.singleton |> tagOrUpper
        /// x..
        let stringOrUpper lowerBound = lowerBound |> String |> Type.literalType |> List.singleton |> tagOrUpper
        /// ..tag
        let tagOrLower upperBound = ofSpace([], upperBound)
        let multiElementType et = MultiElementTypeConstraint et |> Constraints.makeWithEmptyLocation

        let renumberParameters c =
            ParameterIdReplacers.toReducer ParameterIdCollectors.constraints ParameterIdReplacers.constraints c

        let simplifyTrivias = TriviaSimplifiers.toReducer TriviaSimplifiers.constraints

        let normalize c =
            c
            |> Reducer.repeat 100 (Reducer.mergeMany [
                ConstraintSimplifiers.toReducer ConstraintSimplifiers.constraints
                renumberParameters
            ])
            |> Reducer.once simplifyTrivias

    module Scheme =
        let renumberParameters t =
            ParameterIdReplacers.toReducer ParameterIdCollectors.type' ParameterIdReplacers.type' t

        let simplifyConstraints t =
            ConstraintSimplifiers.toReducer ConstraintSimplifiers.type' t

        let simplifyTrivias t =
            TriviaSimplifiers.toReducer TriviaSimplifiers.type' t

        /// normalize (type('123) -> (?a, ?b: ..string, '123)) =
        ///           (type('0, '1) -> ('1, string, '0))
        let normalize t =
            Scheme.generalize 0 t
            |> Reducer.repeat 100 (Reducer.mergeMany [
                simplifyConstraints
                renumberParameters
            ])
            |> Reducer.once simplifyTrivias

    let scheme = function
        | [], t -> t
        | ps, t -> TypeAbstraction(ps, t) |> Type.makeWithEmptyLocation

    module MultiType =
        let newVarWith level = function
            | ValueSome c -> Type.newVarWith "" level types'.multiKind c |> Type.makeWithEmptyLocation
            | _ -> TypeSystem.Type.newVar "" level types'.multiKind |> Type.makeWithEmptyLocation

        let newVar level = newVarWith level ValueNone

        let normalizeParameterId m =
            let ids = newEmptyState()
            ParameterIdCollectors.type' ids m
            ParameterIdReplacers.type' ids m

    module Declaration =
        let normalize d = {
            d with scheme = Scheme.normalize d.scheme
        }

    module UnifyError =
        let normalize = function
            | RequireField(actualFields, requireKey, requireType) ->
                RequireField(
                    Map.map (fun _ -> Scheme.normalize) actualFields,
                    requireKey,
                    Scheme.normalize requireType
                )

            | ConstraintAndTypeMismatch(c, t) -> ConstraintAndTypeMismatch(Constraints.normalize c, Scheme.normalize t)
            | ConstraintMismatch(c1, c2) -> ConstraintMismatch(Constraints.normalize c1, Constraints.normalize c2)
            | TypeMismatch(t1, t2) -> TypeMismatch(Scheme.normalize t1, Scheme.normalize t2)
            | UndefinedField(t, k) -> UndefinedField(Scheme.normalize t, k)

            | KindMismatch _
            | UnificationStackTooDeep as x -> x

    module DiagnosticKind =
        let normalize = function
            | K.UnifyError u -> UnifyError.normalize u |> K.UnifyError
            | K.GlobalNameCollision(n, d1, d2, ds) ->
                K.GlobalNameCollision(n, Declaration.normalize d1, Declaration.normalize d2, List.map Declaration.normalize ds)

            | K.UndeterminedGlobalVariableEnvironment(x1, x2) ->
                K.UndeterminedGlobalVariableEnvironment(
                    x1,
                    Map.map (fun _ -> NonEmptyList.map Declaration.normalize) x2
                )

            | K.ExternalModuleError(x1, x2) -> K.ExternalModuleError(x1, Diagnostic.normalize x2)

            | e -> e

    module Diagnostic =
        let normalize (Diagnostic(span, sev, k)) =
            Diagnostic(span, sev, DiagnosticKind.normalize k)

module Helpers =
    open TypeExtensions
    open LuaChecker.TypedSyntaxes

    module FileSystem =
        let memory() =
            let gate = obj()
            let mutable lastWriteTime = System.DateTime.MinValue
            let backingStore = ConcurrentDictionary()
            {
                readAllText = fun x -> lock gate <| fun _ -> snd backingStore.[x]
                writeAllText = fun struct(p, c) -> lock gate <| fun _ ->
                    backingStore.[p] <- (lastWriteTime, c)
                    lastWriteTime <- lastWriteTime.AddMilliseconds 1.

                deleteFile = fun x -> lock gate <| fun _ -> backingStore.TryRemove x |> ignore
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

    let toDocumentPath path =
        let path = Path.ChangeExtension(path, ".lua")
        DocumentPath.ofRelativeUri (System.Uri "file:///C:/") (System.Uri(path, System.UriKind.RelativeOrAbsolute))

    type ProjectAction =
        | AddOrUpdate of path: string * source: string
        | Remove of path: string
        | Check of path: string
        | ParseAndCheck of pathWithVersion: (string * int) * source: string
        | IsAncestor of old: string * young: string

    type ActionResult<'CheckResult,'IsAncestorResult> =
        | CheckResult of 'CheckResult
        | IsAncestorResult of 'IsAncestorResult

    type ProjectConfig<'TypeEnv> = {
        caseSensitiveModuleResolve: bool
        luaPath: string option
        platform: System.PlatformID
        luaExeDir: string option
        withTypeEnv: 'TypeEnv -> 'TypeEnv
        initialGlobalModulePaths: string list
    }
    module ProjectConfig =
        let defaultValue = {
            luaPath = None
            caseSensitiveModuleResolve = false
            platform = System.PlatformID.Win32NT
            luaExeDir = None
            withTypeEnv = id
            initialGlobalModulePaths = ["./standard.d.lua"]
        }
    type SourceConfig = {
        path: string
        source: string
    }
    type CheckConfig<'TypeEnv> = {
        path: string
        sources: SourceConfig list
        projectConfig: ProjectConfig<'TypeEnv>
    }
    let checkCached project path =
        match Project.tryFind path project with
        | ValueNone -> None, Seq.empty, project
        | ValueSome sourceFile ->
            let chunk, diagnostics, project = Checkers.checkSourceFileCached project path sourceFile
            Some chunk, diagnostics, project

    let addInitialGlobalModulesFromRealFileSystem p paths =
        let paths = [ for path in paths do Path.GetFullPath path |> DocumentPath.ofPath ]
        for path in paths do
            p.projectRare.fileSystem.writeAllText(path, File.ReadAllText(DocumentPath.toPathOrFail path))

        addInitialGlobalModules p paths

    let projectActions withConfig actions =
        let fs = FileSystem.memory()
        let config = withConfig ProjectConfig.defaultValue
        let packagePath = TopEnv.packagePath config.luaPath config.platform config.luaExeDir
        let env = standardEnv packagePath
        let env = { env with initialGlobalEnv = { env.initialGlobalEnv with types = config.withTypeEnv env.initialGlobalEnv.types } }
        let p = Project.empty fs env config.caseSensitiveModuleResolve
        let p = addInitialGlobalModulesFromRealFileSystem p config.initialGlobalModulePaths

        let checks, _ =
            actions
            |> List.mapFold (fun p -> function
                | AddOrUpdate(path, source) ->
                    let path = toDocumentPath path
                    fs.writeAllText(path, source.Replace("\r\n", "\n"))
                    let struct(p, _) = addOrUpdateSourceFile path p
                    [], p

                | Remove path ->
                    fs.deleteFile(toDocumentPath path)
                    let struct(p, _) = removeSourceFile (toDocumentPath path) p
                    [], p

                | Check path ->
                    let tree, e, p = checkCached p (toDocumentPath path)
                    [CheckResult(tree, Seq.toList e, [])], p

                | ParseAndCheck((path, version), source) ->
                    let tree, e, p, ds = parseAndCheckCached p (toDocumentPath path) (InMemory(source, version))
                    [CheckResult(Some tree, Seq.toList e, ds)], p

                | IsAncestor(old, young) ->
                    let r = isAncestor (toDocumentPath old) (toDocumentPath young) p
                    [IsAncestorResult r], p

            ) p

        List.concat checks

    /// `fun(…) -> $x` => $x
    let (|FunctionReturnType|_|) = function
        | Type.Function typeEnv' (ValueSome(_, r)) -> r |> Some
        | _ -> None

    /// `()` => nil | `($x, …)` => $x
    let (|MultiToValueType|) = function
        | Type.Cons typeEnv' (ValueSome(t, _)) -> t
        | _ -> types'.nil |> Type.makeWithEmptyLocation

    let (|FunctionReturnType1|_|) = function
        | FunctionReturnType { kind = MultiToValueType x } -> Some x
        | _ -> None

    let rec functionReturnType1Rec t =
        match t.kind with
        // `fun(…) -> ()` => nil
        // `fun(…) -> (t, …)` => t
        | FunctionReturnType1 t -> t
        // `type(…) -> t`
        | TypeAbstraction(ps, t) -> TypeAbstraction(ps, functionReturnType1Rec t) |> Type.makeWithEmptyLocation
        | _ -> t

    let rec functionReturnTypeRec t =
        match t.kind with
        // `fun(…) -> t` => t
        | FunctionReturnType t -> t
        | TypeAbstraction(ps, t) -> TypeAbstraction(ps, functionReturnTypeRec t) |> Type.makeWithEmptyLocation
        | _ -> t

    let chunkReturnType1 t = t.functionType |> functionReturnType1Rec |> Scheme.normalize
    let chunkReturnType t = t.functionType |> functionReturnTypeRec |> Scheme.normalize

    let projectActionsToScheme withConfig =
        projectActions withConfig >> List.map (function
            | IsAncestorResult x -> IsAncestorResult x
            | CheckResult(Some t, [], _) -> CheckResult <| Ok (chunkReturnType1 t)
            | CheckResult(_, e, _) -> CheckResult(Error e)
        )

    let projectSchemes withConfig actions =
        projectActions withConfig actions
        |> List.map (function
            | CheckResult(Some x, [], _) -> Ok <| chunkReturnType1 x
            | CheckResult(_, es, _) -> Error <| List.map Diagnostic.normalize es
            | _ -> Error []
        )

    let projectSchemeAndDiagnostics withConfig actions =
        projectActions withConfig actions
        |> List.map (function
            | CheckResult(Some x, es, _) -> chunkReturnType1 x, List.map Diagnostic.normalize es
            | r -> failwithf "%A" r
        )

    let checkChunk withConfig source =
        let { path = path; sources = sources; projectConfig = projectConfig } = withConfig {
            path = "C:/dir/file.lua"
            sources = []
            projectConfig = ProjectConfig.defaultValue
        }

        let actions = [
            for s in sources do AddOrUpdate(s.path, s.source)
            AddOrUpdate(path, source)
            Check path
        ]

        match projectActions (fun _ -> projectConfig) actions with
        | [CheckResult(scheme, e, _)] -> scheme, e
        | xs -> failwithf "%A" xs

    let chunkDiagnostics withConfig = checkChunk withConfig >> snd >> List.map Diagnostic.normalize
    let chunkSchemeAndDiagnostics withConfig source =
        match checkChunk withConfig source with
        | Some c, es -> chunkReturnType1 c, List.map Diagnostic.normalize es
        | x -> failwithf "%A" x

    let chunkScheme withConfig source =
        let chunk, es = checkChunk withConfig source
        match chunk, es with
        | Some c, [] -> chunkReturnType1 c
        | _ -> failwithf "%A" es

    let chunkResult withConfig source =
        let chunk, es = checkChunk withConfig source
        match chunk, es with
        | Some c, [] -> chunkReturnType c
        | _ -> failwithf "%A" es

    type TypeParameterOption<'c> = {
        kind: Kind
        location: Location list
        name: string
        c: 'c
    }
    type TypeMakeOptions = {
        location: Location list
        normalize: Type -> Type
    }
    let private defP c = {
        kind = types'.valueKind
        location = []
        name = ""
        c = c
    }
    let private defT = {
        location = []
        normalize = Scheme.normalize
    }

    type TypeMakeOptions0 = {
        t: TypeMakeOptions
    }
    let type0With withOptions makeType =
        let o = withOptions {
            t = defT
        }
        makeType()
        |> o.t.normalize

    let type0 t = type0With id <| fun _ -> t

    type MakeConstraints1 = (Type -> Constraints)
    type TypeMakeOptions1 = {
        p0: TypeParameterOption<MakeConstraints1>
        t: TypeMakeOptions
    }
    let type1With withOptions makeType =
        let makeC _ = Constraints.any
        let o = withOptions {
            p0 = defP makeC
            t = defT
        }

        let p0 = TypeParameterId.createNext o.p0.kind
        let t0 = ParameterType p0 |> Type.makeWithLocation o.p0.location
        let p0 = TypeParameter(o.p0.name, p0, o.p0.c t0)

        TypeAbstraction([p0], makeType t0)
        |> Type.makeWithLocation o.t.location
        |> o.t.normalize

    let type1 makeType = type1With id makeType

    type MakeConstraints2 = (Type -> Type -> Constraints)
    type TypeMakeOptions2 = {
        p0: TypeParameterOption<MakeConstraints2>
        p1: TypeParameterOption<MakeConstraints2>
        t: TypeMakeOptions
    }
    let type2With withOptions makeType =
        let makeC _ _ = Constraints.any
        let o = withOptions {
            p0 = defP makeC
            p1 = defP makeC
            t = defT
        }

        let p0 = TypeParameterId.createNext o.p0.kind
        let p1 = TypeParameterId.createNext o.p1.kind
        let t0 = ParameterType p0 |> Type.makeWithLocation o.p0.location
        let t1 = ParameterType p1 |> Type.makeWithLocation o.p1.location
        let p0 = TypeParameter(o.p0.name, p0, o.p0.c t0 t1)
        let p1 = TypeParameter(o.p1.name, p1, o.p1.c t0 t1)

        TypeAbstraction([p0; p1], makeType t0 t1)
        |> Type.makeWithLocation o.t.location
        |> o.t.normalize

    let type2 makeType = type2With id makeType

    type MakeConstraints3 = (Type -> Type -> Type -> Constraints)
    type TypeMakeOptions3 = {
        p0: TypeParameterOption<MakeConstraints3>
        p1: TypeParameterOption<MakeConstraints3>
        p2: TypeParameterOption<MakeConstraints3>
        t: TypeMakeOptions
    }
    let type3With withOptions makeType =
        let makeC _ _ _ = Constraints.any
        let o = withOptions {
            p0 = defP makeC
            p1 = defP makeC
            p2 = defP makeC
            t = defT
        }

        let p0 = TypeParameterId.createNext o.p0.kind
        let p1 = TypeParameterId.createNext o.p1.kind
        let p2 = TypeParameterId.createNext o.p2.kind
        let t0 = ParameterType p0 |> Type.makeWithLocation o.p0.location
        let t1 = ParameterType p1 |> Type.makeWithLocation o.p1.location
        let t2 = ParameterType p2 |> Type.makeWithLocation o.p2.location
        let p0 = TypeParameter(o.p0.name, p0, o.p0.c t0 t1 t2)
        let p1 = TypeParameter(o.p1.name, p1, o.p1.c t0 t1 t2)
        let p2 = TypeParameter(o.p2.name, p2, o.p2.c t0 t1 t2)

        TypeAbstraction([p0; p1; p2], makeType t0 t1 t2)
        |> Type.makeWithLocation o.t.location
        |> o.t.normalize

    let type3 makeType = type3With id makeType

    let forall1With kind0 f =
        let p0 = TypeParameterId.createNext kind0
        let t0 = ParameterType p0 |> Type.makeWithEmptyLocation
        let c0, t = f t0
        scheme([TypeParameter("", p0, c0)], t) |> Scheme.normalize

    let forall1 = forall1With types'.valueKind

    let forall2With (kind0, kind1) f =
        let p0 = TypeParameterId.createNext kind0
        let p1 = TypeParameterId.createNext kind1
        let t0 = ParameterType p0 |> Type.makeWithEmptyLocation
        let t1 = ParameterType p1 |> Type.makeWithEmptyLocation
        let (c0, c1), t = f t0 t1
        scheme([TypeParameter("", p0, c0); TypeParameter("", p1, c1)], t) |> Scheme.normalize

    let forall2 = forall2With (types'.valueKind, types'.valueKind)

    let scheme1With (kind0, c0) makeType =
        type1With (fun c -> { c with p0 = { c.p0 with kind = kind0; c = fun _ -> c0 }}) makeType

    let scheme2With ((k0, c0), (k1, c1)) makeType =
        type2With (fun c ->
            { c with
                p0 = { c.p0 with kind = k0; c = fun _ _ -> c0 }
                p1 = { c.p1 with kind = k1; c = fun _ _ -> c1 }
            })
            makeType

    let scheme3With ((k0, c0), (k1, c1), (k2, c2)) makeType =
        type3With (fun c ->
            { c with
                p0 = { c.p0 with kind = k0; c = fun _ _ _ -> c0 }
                p1 = { c.p1 with kind = k1; c = fun _ _ _ -> c1 }
                p2 = { c.p2 with kind = k2; c = fun _ _ _ -> c2 }
            })
            makeType

    let type1WithConstraints c0 makeType =
        type1With (fun c ->
            { c with
                p0 = { c.p0 with c = fun _ -> c0 }
            })
            makeType

    let type2WithConstraints (c0, c1) makeType =
        type2With (fun c ->
            { c with
                p0 = { c.p0 with c = fun _ _ -> c0 }
                p1 = { c.p1 with c = fun _ _ -> c1 }
            })
            makeType

    let type3WithConstraints (c0, c1, c2) makeType =
        type3With (fun c ->
            { c with
                p0 = { c.p0 with c = fun _ _ _ -> c0 }
                p1 = { c.p1 with c = fun _ _ _ -> c1 }
                p2 = { c.p2 with c = fun _ _ _ -> c2 }
            })
            makeType

    /// `(t, v)`
    let (^^) t v = types'.cons(t, v) |> Type.makeWithEmptyLocation
    /// `(x0, x1, … xn)`
    let multi xs = List.foldBack (^^) xs (types'.empty |> Type.makeWithEmptyLocation)
    /// `fun(t1): t2`
    let (->.) t1 t2 = types'.fn(multi t1, multi t2) |> Type.makeWithEmptyLocation
    /// `table<number, e>`
    let arrayT e = types'.table(types'.number |> Type.makeWithEmptyLocation, e) |> Type.makeWithEmptyLocation
    /// typeof x
    let numberT x = types'.literal(Number x, [])
    /// typeof x
    let stringT x = types'.literal(String x, [])
    /// typeof x
    let booleanT x = types'.literal((if x then True else False), [])

    let location documentPath (start, end') = Location(toDocumentPath documentPath, { start = start; end' = end' })
    let error (start, end') k = Diagnostic({ start = start; end' = end' }, Severity.Error, k)
    let warning (start, end') k = Diagnostic({ start = start; end' = end' }, Severity.Warning, k)
    let info (start, end') k = Diagnostic({ start = start; end' = end' }, Severity.Info, k)
    let typeMismatchError (p1, p2) (t1, t2) = TypeMismatch(t1, t2) |> K.UnifyError |> error (p1, p2)

    /// AddOrUpdate
    let (&>) source path = AddOrUpdate(path, source)
    /// ParseAndCheck
    let (&><) source path = ParseAndCheck(path, source)

    let unify t1 t2 = Type.unify typeEnv' t1 t2

    type EmptyLocationTypes = {
        multiKind: Kind
        valueKind: Kind
        empty: Type
        nil: Type
        number: Type
        string: Type
        boolean: Type
        fn: struct(Type * Type) -> Type
        table: struct(Type * Type) -> Type
        multi1: Type -> Type
    }
    let types = {
        multiKind = types'.multiKind
        valueKind = types'.valueKind
        empty = Type.empty
        nil = types'.nil |> Type.makeWithEmptyLocation
        number = types'.number |> Type.makeWithEmptyLocation
        string = types'.string |> Type.makeWithEmptyLocation
        boolean = types'.boolean |> Type.makeWithEmptyLocation
        fn = types'.fn >> Type.makeWithEmptyLocation
        table = types'.table >> Type.makeWithEmptyLocation
        multi1 = fun t -> TypeSystem.multi1 types' t []
    }
    [<Struct>]
    type PolymorphicTypedSyntaxVisitor<'T when 'T :> ITypedSyntaxVisitor and 'T : not struct>(visitor: 'T) =
        interface ITypedSyntaxVisitor with
            override _.Var(x1, x2) = visitor.Var(x1, x2)
            override _.Reserved(x1, x2) = visitor.Reserved(x1, x2)
            override _.Literal(x1, x2, x3, x4) = visitor.Literal(x1, x2, x3, x4)

            override _.DocumentReserved x = visitor.DocumentReserved x
            override _.DocumentIdentifier x = visitor.DocumentIdentifier x
            override _.DocumentFieldSeparator x = visitor.DocumentFieldSeparator x
            override _.DocumentFieldIdentifier x = visitor.DocumentFieldIdentifier x
            override _.DocumentFieldVisibility x = visitor.DocumentFieldVisibility x
    let polyVisitor v = PolymorphicTypedSyntaxVisitor v

    module D = LuaChecker.Syntax.Documents
    [<AbstractClass>]
    type TypedSyntaxVisitorBase() =
        abstract Visit: unit -> unit

        abstract Var: Var * TypeEnvironment -> unit
        default v.Var(_, _) = v.Visit()
        abstract Reserved: ReservedVar * TypeEnvironment -> unit
        default v.Reserved(_, _) = v.Visit()
        abstract Literal: Syntaxes.Literal * Type * TypeEnvironment * LeafInfo voption -> unit
        default v.Literal(_, _, _, _) = v.Visit()

        abstract DocumentReserved: LeafSemantics D.Reserved -> unit
        default v.DocumentReserved _ = v.Visit()
        abstract DocumentIdentifier: LeafSemantics D.Identifier -> unit
        default v.DocumentIdentifier _ = v.Visit()
        abstract DocumentFieldSeparator: LeafSemantics D.FieldSeparator -> unit
        default v.DocumentFieldSeparator _ = v.Visit()
        abstract DocumentFieldIdentifier: LeafSemantics D.FieldIdentifier -> unit
        default v.DocumentFieldIdentifier _ = v.Visit()
        abstract DocumentFieldVisibility: LeafSemantics D.FieldVisibility -> unit
        default v.DocumentFieldVisibility _ = v.Visit()

        interface ITypedSyntaxVisitor with
            override v.Var(x1, x2) = v.Var(x1, x2)
            override v.Reserved(x1, x2) = v.Reserved(x1, x2)
            override v.Literal(x1, x2, x3, x4) = v.Literal(x1, x2, x3, x4)

            override v.DocumentReserved x = v.DocumentReserved x
            override v.DocumentIdentifier x = v.DocumentIdentifier x
            override v.DocumentFieldSeparator x = v.DocumentFieldSeparator x
            override v.DocumentFieldIdentifier x = v.DocumentFieldIdentifier x
            override v.DocumentFieldVisibility x = v.DocumentFieldVisibility x
