[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module rec LuaChecker.TypeSystem
open Cysharp.Text
open System.Collections.Generic
open System.Threading
open Result.Operators
open LuaChecker.Primitives
open LuaChecker.Primitives.TrampolineOperators
module S = Syntaxes
module VOption = ValueOption


module TypeParameterId =
    let private nextId = ref 0L
    let createNext kind = TypeParameterId(Interlocked.Increment &nextId.contents, kind)

module TypeParameter =
    let createNextWith displayName kind constraints = TypeParameter(displayName, TypeParameterId.createNext kind, constraints)
    let createNext displayName kind = createNextWith displayName kind Constraints.any

let context = trampoline
let adjustVarLevel v v2 =
    match v.target, v2.target with
    | Var(l, _), Var(l2, c2) when l < l2 ->
        let level = l
        v2.target <- Var(level, c2)
    | _ -> ()

module Fields =
    let show fields =
        use mutable b = ZString.CreateStringBuilder()
        let mutable state = TypePrintState.create TypeWriteOptions.Default
        let scope = TypePrintScope.empty
        FieldsExtensions.Append(&b, fields, &scope, &state)
        b.ToString()

module Constraints =
    let makeWithLocation location c: Constraints = { trivia = location; kind = c }
    let makeWithEmptyLocation c = makeWithLocation [] c
    let withEntity c x: Constraints = { c with kind = x }
    let any = InternalConstraints.any

    let isAny c = InternalConstraints.isAny c
    let hasField = function
        | { kind = InterfaceConstraint fs } -> Map.isEmpty fs |> not
        | _ -> false

    let ofInterfaceType fields = InterfaceConstraint fields
    /// v..
    let literal1 location v = UnionConstraint(lowerBound = TypeSet [Type.makeWithLocation location <| LiteralType v], upperBound = UniversalTypeSet)
    let freeVars' env vars c =
        match c.kind with
        | InterfaceConstraint fs -> Map.fold (fun vars _ t -> Type.freeVars' env vars t) vars fs
        | MultiElementTypeConstraint t -> Type.freeVars' env vars t
        | UnionConstraint(lower, upper) ->
            let vars = TypeSet.toList lower |> List.fold (Type.freeVars' env) vars
            TypeSet.toList upper |> List.fold (Type.freeVars' env) vars

    let apply vs c =
        match c.kind with
        | InterfaceConstraint fs ->
            Map.map (fun _ t -> Type.apply vs t) fs |> InterfaceConstraint

        | MultiElementTypeConstraint t ->
            Type.apply vs t |> MultiElementTypeConstraint

        | UnionConstraint(lower, upper) ->
            let lower = TypeSet.map (Type.apply vs) lower
            let upper = TypeSet.map (Type.apply vs) upper
            UnionConstraint(lower, upper)

        |> withEntity c

    let instantiate' vs c =
        match c.kind with
        | InterfaceConstraint fs ->
            Map.map (fun _ t -> Type.instantiate' vs t) fs |> InterfaceConstraint

        | MultiElementTypeConstraint t ->
            Type.instantiate' vs t |> MultiElementTypeConstraint

        | UnionConstraint(lower, upper) ->
            let lower = TypeSet.map (Type.instantiate' vs) lower
            let upper = TypeSet.map (Type.instantiate' vs) upper
            UnionConstraint(lower, upper)

        |> withEntity c

    let show c =
        use mutable b = ZString.CreateStringBuilder()
        let mutable state = TypePrintState.create TypeWriteOptions.Default
        let scope = TypePrintScope.empty
        ConstraintsExtensions.AppendConstraints(&b, c, &scope, &state)
        b.ToString()

module Kind =
    let unify k1 k2 = unifyKind k1 k2 |> Trampoline.run |> Result.tryToErrorV
    let show kind =
        use mutable b = ZString.CreateStringBuilder()
        let options = TypeWriteOptions.Default
        let mutable state = TypePrintState.create options
        let scope = TypePrintScope.empty
        KindExtensions.Append(&b, kind, &scope, &state)
        b.ToString()

[<Struct>]
type TypeVisitEnv<'T> = {
    visitedVars: VarTypeSite list
    other: 'T
}
module TypeVisitEnv =
    let empty = { visitedVars = []; other = () }

[<Struct>]
type FreeVarsEnv = {
    level: int
}

[<Struct>]
type UnifyTypeEnv = {
    visitedVarToType: Assoc<VarTypeSite, Type>
}
[<Struct>]
type UnifyEnv = {
    types: TypeEnv
    unifyDepth: int
}
module UnifyEnv =
    let empty = {
        visitedVarToType = Assoc.empty
    }

let addVar v env =
    if List.contains v env.visitedVars then ValueNone else
    ValueSome { env with visitedVars = v::env.visitedVars }

type TypeEnv = {
    system: TypeSystem
    stringTableTypes: Type list
}

module Type =
    let withEntity t x: Type = { t with kind = x }
    let makeWithLocation location t: Type = { kind = t; trivia = location }
    let makeWithEmptyLocation t = makeWithLocation [] t

    /// `fun(…): (…)`
    let (|Function|) types t = types.system.unFn t
    /// `()`
    let (|IsEmpty|) types = function
        | NamedType(t, _) -> types.system.emptyConstant = t
        | _ -> false
    /// `(::)`
    let (|Cons|) types t = types.system.unCons t
    /// `...`
    let (|MultiVar|) types = function
        | VarType({ varKind = k } as r) when k = types.system.multiKind -> ValueSome r
        | _ -> ValueNone

    /// `'m...`
    let (|MultiParameter|) types = function
        | ParameterType(TypeParameterId(_, k) as p) when k = types.system.multiKind -> ValueSome p
        | _ -> ValueNone

    let newVarWith displayName level kind c = VarType(Var.newVarWith displayName level kind c)
    let newVar displayName level kind = newVarWith displayName level kind Constraints.any

    let freeVars' env vars t =
        match t.kind with
        | NamedType(_, []) -> vars
        | NamedType(_, ts) -> List.fold (freeVars' env) vars ts
        | LiteralType _ -> vars
        | InterfaceType fs -> Map.fold (fun vs _ t -> freeVars' env vs t) vars fs

        | VarType r ->
            match addVar r env with
            | ValueNone -> vars
            | ValueSome env ->

            match r.target with
            | Assigned t -> freeVars' env vars t
            | Var(l, c) ->

            let vars =
                if env.other.level < l && not <| List.exists (fun struct(r', _) -> LanguagePrimitives.PhysicalEquality r r') vars
                then struct(r, c)::vars
                else vars

            Constraints.freeVars' env vars c

        | ParameterType _ -> vars

        | TypeAbstraction([], t) -> freeVars' env vars t
        | TypeAbstraction(ps, t) ->
            let vars = List.fold (fun vars (TypeParameter(_, _, c)) -> Constraints.freeVars' env vars c) vars ps
            freeVars' env vars t

    let freeVars level t =
        let env = {
            other = { level = level }
            visitedVars = []
        }
        List.rev <| freeVars' env [] t

    let apply vs t =
        match t.kind with
        | NamedType(_, []) -> t
        | NamedType(n, ts) -> NamedType(n, List.map (apply vs) ts) |> withEntity t
        | LiteralType _ -> t
        | InterfaceType fs -> Map.map (fun _ -> apply vs) fs |> InterfaceType |> withEntity t
        | VarType r ->
            match addVar r vs with
            | ValueNone -> t
            | ValueSome vs ->

            match r.target with
            | Assigned t -> apply vs t
            | Var _ ->

            match Assoc.tryFind r vs.other with
            | ValueSome(TypeParameter(_, p, _)) -> ParameterType p |> withEntity t
            | _ -> t

        | ParameterType _ -> t
        | TypeAbstraction([], t) -> apply vs t
        | TypeAbstraction(ps, t) ->
            let ps = List.map (fun (TypeParameter(n, id, c)) -> TypeParameter(n, id, Constraints.apply vs c)) ps
            match apply vs t with
            | { kind = TypeAbstraction(ps', et) } as t -> TypeAbstraction(ps@ps', et) |> withEntity t
            | et -> TypeAbstraction(ps, et) |> withEntity t

    let assign vs t =
        match t.kind with
        | NamedType(_, ts) -> for t in ts do assign vs t
        | LiteralType _ -> ()
        | InterfaceType fs -> for kv in fs do assign vs kv.Value
        | VarType r ->
            match Assoc.tryFind r vs with
            | ValueSome(TypeParameter(_, p, _)) ->
                r.target <- Assigned <| makeWithEmptyLocation (ParameterType p)
            | _ -> ()

        | ParameterType _ -> ()
        | TypeAbstraction([], t) -> assign vs t
        | TypeAbstraction(ps, t) ->
            for TypeParameter(_, _, c) in ps do
                match c.kind with
                | MultiElementTypeConstraint t -> assign vs t
                | InterfaceConstraint fs ->
                    for kv in fs do assign vs kv.Value

                | UnionConstraint(lower, upper) ->
                    for t in TypeSet.toList lower do assign vs t
                    for t in TypeSet.toList upper do assign vs t

            assign vs t

    let show t =
        match t.kind with
        | VarType { target = Assigned t } -> show t
        | NamedType(TypeConstant(name, _), []) -> name
        | t ->
            use mutable b = ZString.CreateStringBuilder()
            let mutable state = TypePrintState.create TypeWriteOptions.Default
            let scope = TypePrintScope.empty
            b.Append(t, &scope, &state)
            b.ToString()

    let instantiate' vs t =
        match t.kind with
        | NamedType(n, ts) -> NamedType(n, List.map (instantiate' vs) ts) |> withEntity t
        | LiteralType _ -> t
        | InterfaceType fs -> Map.map (fun _ v -> instantiate' vs v) fs |> InterfaceType |> withEntity t
        | VarType r ->
            match addVar r vs with
            | ValueNone -> t
            | ValueSome vs ->

            match r.target with
            | Assigned t -> instantiate' vs t
            | Var _ -> t

        | ParameterType p ->
            match Assoc.tryFind p vs.other with
            | ValueSome t -> t
            | _ -> t

        | TypeAbstraction([], t) -> instantiate' vs t
        | TypeAbstraction(ps, et) ->
            let ps = List.map (fun (TypeParameter(n, id, c)) -> TypeParameter(n, id, Constraints.instantiate' vs c)) ps
            TypeAbstraction(ps, instantiate' vs et)
            |> withEntity t

    let unify types t1 t2 =
        let env = {
            types = types
            unifyDepth = 0
        }
        match unifyType env UnifyEnv.empty UnifyEnv.empty t1 t2 |> Trampoline.run with
        | Ok() -> ValueNone
        | Error e -> ValueSome e

    let kind types t =
        match t.kind with
        | NamedType(TypeConstant(_, k), _) ->
            match k with
            | NamedKind _ -> k
            | FunKind(_, k) -> k

        | LiteralType _
        | InterfaceType _ -> types.system.valueKind
        | TypeAbstraction(_, t) -> kind types t
        | ParameterType(TypeParameterId(_, k))
        | VarType { varKind = k } -> k

module TypeSet =
    type TypeKey =
        | LiteralKey of S.LiteralKind
        | NamedKey of TypeConstant * TypeKey list

    let normalize = function
        | TypeSet((_::_::_) as ts) ->
            let rec comparable t =
                match t.kind with
                | LiteralType _ -> true
                | NamedType(_, ts) -> List.forall comparable ts
                | _ -> false

            let rec key t =
                match t.kind with
                | LiteralType k -> LiteralKey k
                | NamedType(t, ts) -> NamedKey(t, List.map key ts)
                | _ -> failwith ""

            let comparableTypes, ts = List.partition comparable ts
            let sortedTypes = List.sortBy key comparableTypes
            sortedTypes @ ts
            |> TypeSet

        | ts -> ts

    exception TypeComparisonException of Type * Type

    // TODO:
    ///<summary>t1 ⊆ t2</summary>
    ///<exception cref="TypeComparisonException" />
    let isSubsetOrRaise types t1 t2 =
        match t1.kind, t2.kind with
        | NamedType(k1, ts1), NamedType(k2, ts2) ->
            if k1 <> k2 then false else
            let rec aux = function
                | [], [] -> true
                | t1::ts1, t2::ts2 ->
                    if isSubsetOrRaise types t1 t2 then aux (ts1, ts2)
                    else false

                | _ -> false
            aux (ts1, ts2)

        | LiteralType k1, LiteralType k2 ->
            Syntax.LiteralKind.equalsER k1 k2

        | NamedType _, LiteralType _ -> false

        | LiteralType k1, NamedType(c2, _) ->
            match k1 with

            // nil ⊆ nil
            | S.Nil -> false

            // true ⊆ boolean
            | S.True | S.False -> c2 = types.booleanConstant

            // 1 ⊆ number
            | S.Number _ -> c2 = types.numberConstant

            // 'a' ⊆ string
            | S.String _ -> c2 = types.stringConstant

        | _ -> raise <| TypeComparisonException(t1, t2)

    ///<exception cref="TypeComparisonException" />
    let equalsOrRaise types t1 t2 = isSubsetOrRaise types t1 t2 && isSubsetOrRaise types t2 t1

    /// ts1 ⊆ ts2
    let isSubset types ts1 ts2 =
        try
            match ts1, ts2 with
            | _, UniversalTypeSet -> Ok true
            | UniversalTypeSet, TypeSet _ -> Ok false

            | TypeSet ts1, TypeSet ts2 ->

            ts1
            |> List.forall (fun t1 ->
                List.exists (isSubsetOrRaise types t1) ts2
            )
            |> Ok
        with
        | TypeComparisonException(t1, t2) -> Error <| TypeMismatch(t1, t2)

    let union types ts1 ts2 =
        let rec add ts1 t2 =
            match List.tryRemove (equalsOrRaise types t2) ts1 with
            | ValueSome(t, ts1) -> ts1 @ [Type.makeWithLocation (t.trivia @ t2.trivia) t2.kind]
            | _ -> ts1 @ [t2]

        try
            match ts1, ts2 with
            | UniversalTypeSet, _ | _, UniversalTypeSet -> Ok UniversalTypeSet

            | TypeSet ts1, TypeSet ts2 ->

            List.fold add ts1 ts2
            |> TypeSet
            |> normalize
            |> Ok
        with
        | TypeComparisonException(t1, t2) ->
            Error <| TypeMismatch(t1, t2)

    let intersect types ts1 ts2 =
        try
            match ts1, ts2 with
            | UniversalTypeSet, ts | ts, UniversalTypeSet -> Ok ts
            | TypeSet ts1, TypeSet ts2 ->
                ts1
                |> List.choose (fun t1 ->
                    match List.tryFind (equalsOrRaise types t1) ts2 with
                    | Some t2 -> Type.makeWithLocation (t1.trivia @ t2.trivia) t2.kind |> Some
                    | _ -> None
                )
                |> TypeSet
                |> normalize
                |> Ok
        with
        | TypeComparisonException(t1, t2) ->
            Error <| TypeMismatch(t1, t2)

let occur env r t =
    match t.kind with
    | VarType r' ->
        if r' = r then true else
        match addVar r' env with
        | ValueNone -> false
        | ValueSome env ->

        match r'.target with
        | Var _  -> adjustVarLevel r r'; false
        | Assigned t -> occur env r t

    | NamedType(_, ts) -> List.exists (occur env r) ts
    | LiteralType _ -> false
    | InterfaceType fs -> Map.exists (fun _ t -> occur env r t) fs
    | ParameterType _ -> false
    | TypeAbstraction([], t) -> occur env r t
    | TypeAbstraction(ps, t) ->
        List.exists (fun (TypeParameter(_, _, c)) ->
            match c.kind with
            | InterfaceConstraint fs ->
                if Map.isEmpty fs then false else
                Map.exists (fun _ t -> occur env r t) fs

            | MultiElementTypeConstraint t -> occur env r t
            | UnionConstraint(lower, upper) ->
                TypeSet.toList lower |> List.exists (occur env r) ||
                TypeSet.toList upper |> List.exists (occur env r)
        ) ps ||
        occur env r t

type UnifyError =
    | TypeMismatch of Type * Type
    | RequireField of actualFields: Map<FieldKey, Type> * requireKey: FieldKey * requireType: Type
    | UndefinedField of selfType: Type * fieldKey: FieldKey
    | KindMismatch of Kind * Kind
    | ConstraintMismatch of Constraints * Constraints
    | ConstraintAndTypeMismatch of Constraints * Type
    | UnificationStackTooDeep

let unifyError e = Trampoline.Failure e

let unifyKindList (all1, all2) (ks1, ks2) =
    let rec aux ks1 ks2 = context {
        match ks1, ks2 with
        | [], [] -> return ()
        | k1::ks1, k2::ks2 ->
            do! unifyKind k1 k2
            return! aux ks1 ks2
        | _ ->
            return! unifyError(KindMismatch(all1, all2))
    }
    aux ks1 ks2

let unifyKind k1 k2 = context {
    match k1, k2 with
    | NamedKind n1, NamedKind n2 when n1 = n2 -> return ()

    | (FunKind(ks1, k1) as kind1), (FunKind(ks2, k2) as kind2) ->
        do! unifyKindList (kind1, kind2) (ks1, ks2)
        return! unifyKind k1 k2

    | _ -> return! unifyError(KindMismatch(k1, k2))
}
let findMissingKeyValue map1 map2 =
    map1
    |> Map.tryPick(fun k1 v1 ->
        if not <| Map.containsKey k1 map2
        then Some struct(k1, v1)
        else None
    )

let missingFieldError fs1 fs2 =
    match findMissingKeyValue fs1 fs2 with
    | Some(k1, v1) -> RequireField(fs2, k1, v1)
    | _ ->

    match findMissingKeyValue fs2 fs1 with
    | Some(k2, v2) -> RequireField(fs1, k2, v2)
    | _ -> failwith ""

let unifyList env env1 env2 all1 all2 ts1 ts2 = context {
    match ts1, ts2 with
    | [], [] -> return ()
    | t1::ts1, t2::ts2 ->
        do! unify env env1 env2 t1 t2
        return! unifyList env env1 env2 all1 all2 ts1 ts2

    | _ -> return! unifyError(TypeMismatch(all1, all2))
}
let unifyMap env env1 env2 all1 all2 (e1: IEnumerator<KeyValuePair<FieldKey, Type>>) (e2: IEnumerator<KeyValuePair<FieldKey, Type>>) = context {
    match e1.MoveNext(), e2.MoveNext() with
    | false, false -> return ()
    | true, true ->
        let kv1 = e1.Current
        let kv2 = e2.Current
        if kv1.Key <> kv2.Key then return! unifyError <| missingFieldError all1 all2 else

        do! unify env env1 env2 kv1.Value kv2.Value
        return! unifyMap env env1 env2 all1 all2 e1 e2

    | _ -> return! unifyError <| missingFieldError all1 all2
}

/// `unifyType` との違いは
/// - 定数的なスタック消費量
/// - `Trampoline` のためにヒープを確保する
let unify env env1 env2 t1 t2 =
    if 1024 < env.unifyDepth then unifyError UnificationStackTooDeep else
    let env = { env with unifyDepth = env.unifyDepth + 1 }
    Trampoline.TailCall(fun () -> unifyType env env1 env2 t1 t2)

/// `unify` との違いは
/// - 末尾再帰でないので、複雑な型を渡されるとスタックがあふれる場合がある
/// - 単純な型を渡された場合、ヒープを確保しないため高速
let unifyType env env1 env2 t1 t2 = context {
    match t1.kind, t2.kind with
    | NamedType(n1, ts1), NamedType(n2, ts2) ->
        if n1 <> n2 then return! unifyError(TypeMismatch(t1, t2)) else

        match ts1, ts2 with
        | [], [] -> return ()
        | _ -> return! unifyList env env1 env2 t1 t2 ts1 ts2

    | LiteralType v1, LiteralType v2 ->
        if Syntax.LiteralKind.equalsER v1 v2
        then return ()
        else return! unifyError(TypeMismatch(t1, t2))

    | InterfaceType fs1, InterfaceType fs2 ->
        if Map.count fs1 <> Map.count fs2 then return! unifyError <| missingFieldError fs1 fs2 else

        let e1 = (fs1 :> _ seq).GetEnumerator()
        let e2 = (fs2 :> _ seq).GetEnumerator()
        return! unifyMap env env1 env2 fs1 fs2 e1 e2

    | ParameterType p1, ParameterType p2 ->
        if p1 = p2 then return () else
        return! unifyError(TypeMismatch(t1, t2))

    // unify ?a ?a = []
    // unify (?a := x) (?a := x) = []
    | VarType r1, VarType r2 when LanguagePrimitives.PhysicalEquality r1 r2 -> return ()

    // unify (?x := a) x
    | VarType({ target = Assigned at1 } as r1), _ -> return! unifyAssignedTypeAndType env env1 env2 (at1, r1, t1) t2
    | _, VarType({ target = Assigned at2 } as r2) -> return! unifyAssignedTypeAndType env env2 env1 (at2, r2, t2) t1

    | TypeAbstraction([], t1), _ -> return! unify env env1 env2 t1 t2
    | _, TypeAbstraction([], t2) -> return! unify env env1 env2 t1 t2

    | VarType({ target = Var(l1, c1) } as r1), _ -> return! unifyVarAndType env env1 env2 (l1, c1, r1, t1) t2
    | _, VarType({ target = Var(l2, c2) } as r2) -> return! unifyVarAndType env env2 env1 (l2, c2, r2, t2) t1

    // TODO:
    | TypeAbstraction(TypeParameter(_, TypeParameterId(id1, _), _)::_, _),
        TypeAbstraction(TypeParameter(_, TypeParameterId(id2, _), _)::_, _) when id1 = id2 -> return ()

    | TypeAbstraction _, _ -> return! unifyAbstractionAndType env env1 env2 t1 t2
    | _, TypeAbstraction _ -> return! unifyAbstractionAndType env env2 env1 t2 t1

    | _ -> return! unifyError(TypeMismatch(t1, t2))
}
let unifyAssignedTypeAndType env env1 env2 (at1, r1, t1) t2 = context {
    match Assoc.tryFind r1 env1.visitedVarToType with

    // unify (?t1 :=(not rec) at1) t2 = unify at1 t2
    | ValueNone ->
        let env1 = { env1 with visitedVarToType = Assoc.add r1 t2 env1.visitedVarToType }
        return! unify env env1 env2 at1 t2

    // unify (?t1 :=(rec(?fr2)) at1) t2
    | ValueSome { kind = VarType({ target = Assigned _ } as fr2) } ->

        match t2.kind with
        | VarType({ target = Assigned at2 } as r2) ->

            // unify (?t1 :=(rec(?fr2)) at1) ?fr2 = Ok
            if fr2 = r2 then return () else

            match Assoc.tryFind r2 env2.visitedVarToType with

            // unify (?t1 :=(rec(?fr2)) at1) (?t2 =?(rec) at2) = Error occur
            | ValueSome _ -> return! unifyError(TypeMismatch(t1, t2))

            // unify (?t1 :=(rec(?fr2)) at1) (?t2 =?(not rec) at2) = unify at1 at2
            | _ ->
                let env2 = { env2 with visitedVarToType = Assoc.add r2 t1 env2.visitedVarToType }
                return! unify env env1 env2 at1 at2

        // unify (?t1 :=(rec(?fr2)) at1) t2 = unify at1 t2
        | _ ->
            return! unify env env1 env2 at1 t2

    // unify (?t1 :=(rec(ft2)) at1) t2
    | ValueSome _ -> return! unify env env1 env2 at1 t2
}
let tryAddVisitedVar env1 (r1, c1) t2 = result {
    match Assoc.tryFind r1 env1.visitedVarToType with

    // unify [?t1,f2] (?t1: … ?t1 …)
    | ValueSome f2 -> return! Error f2
    | _ ->

    // 循環するのは制約付き型変数のみ
    if Constraints.isAny c1 then return env1

    else return { env1 with visitedVarToType = Assoc.add r1 t2 env1.visitedVarToType }
}
let unifyVarAndType env env1 env2 (_, c1, r1, t1) t2 = context {
    occur TypeVisitEnv.empty r1 t2 |> ignore

    match t2.kind with
    | VarType({ target = Assigned at2 } as r2) -> return! unifyAssignedTypeAndType env env2 env1 (at2, r2, t2) t1
    | VarType({ target = Var(l2, c2) } as r2) ->

        // c1 内を探索するので循環チェックが必要
        match tryAddVisitedVar env1 (r1, c1) t2 with
        | Error _ ->
            // TODO:
            return ()

        | Ok env1 ->

        do! unifyKind r1.varKind r2.varKind
        let f1, env2 =
            match Assoc.tryFind r2 env2.visitedVarToType with
            | ValueSome _ as f1 -> f1, env2
            | f1 -> f1, { env2 with visitedVarToType = Assoc.add r2 t1 env2.visitedVarToType }

        let! c = unifyConstraints env env1 env2 (c1, r1, t1) (c2, r2, t2)

        // unify (?t1: c1) (?t2: c2) = [?t3: unify c1 c2; ?t1 := ?t3; ?t2 := ?t3]
        let location3 = t1.trivia @ t2.trivia
        let t3 = Type.newVarWith "" l2 r2.varKind c |> Type.makeWithLocation location3
        r2.target <- Assigned t3
        r1.target <- Assigned t3

        match f1 with
        | ValueSome { kind = TypeAbstraction _ } ->
            // TODO:
            return ()

        | ValueSome f1 -> return! unify env env1 env2 f1 t2
        | _ -> return ()

    | InterfaceType _
    | NamedType _
    | LiteralType _ ->

        // c1 内を探索するので循環チェックが必要
        match tryAddVisitedVar env1 (r1, c1) t2 with
        | Error _ -> return! unifyError(TypeMismatch(t1, t2))
        | Ok env1 ->

        do! unifyKind r1.varKind (Type.kind env.types t2)
        do! matchConstraints env env1 env2 (c1, r1, t1) t2

        // f: type ('t: { x: number }). ('t, 't) -> 't
        // f({ x = 10, y = 20 }, { x = 10 })
        //
        // [generalize] f: (?a, ?a) -> (?a: { x: number })
        // [unify] (?a: { x: number }) { x: number, y: number } => [?a = { x: number, y: number }]
        // [unify] (?a := { x: number, y: number }) { x: number } = Some(RequireField("y"))
        r1.target <- Assigned t2
        return ()

    // unify ?v 'a
    | ParameterType _ ->
        // TODO:
        return! unifyError(TypeMismatch(t1, t2))

    // unify ?v (type 'a. t)
    | TypeAbstraction _ ->
        // ここでは直接 c1 内を探索しないので循環チェック不要
        return! unifyAbstractionAndType env env2 env1 t2 t1
}
// unify ('a: { f: ?af }) ('b: { f: ?bf; g: ?bg }) = unify ?af ?bf @ ['a = 'b; 'a: { f: ?af, g: ?bg }]
// unify ('a: { f: ?af }) { f: ?f } = unify ?af ?f @ ['a = { f: ?af }]
// unify 'a t = ['a = t]
let unifyConstraints ({ types = types } as env) env1 env2 (c1, r1, t1) (c2, r2, t2) = context {
    if Constraints.isAny c1 then return c2 else
    if Constraints.isAny c2 then return c1 else

    match c1.kind, c2.kind with
    | InterfaceConstraint fs1, InterfaceConstraint fs2 ->
        return! unifyInterfaceConstraint env env1 env2 (c1, fs1) (c2, fs2)

    | MultiElementTypeConstraint e1, MultiElementTypeConstraint e2 ->
        do! unify env env1 env2 e1 e2
        return c1

    | UnionConstraint(l1, u1), UnionConstraint(l2, u2) ->
        // unify
        //     ( ( 1 | 'a' )..( 1 | 2 | 3 | 4 | 'a' | 'b' ) )
        //     ( ( 1 | 2 | 3 | 'x' )..( 1 | 2 | 3 | 4 | 5 | 'x' | 'y' ) )
        // = ( ( 1 | 2 | 3 | 'a' | 'x' )..( 1 | 2 | 3 | 4 ) )
        // = Error

        // unifyConstraints `..(number | nil)` `..number` => `..number`
        let! l = TypeSet.union types.system l1 l2 |> Trampoline.ofResult
        let! u = TypeSet.intersect types.system u1 u2 |> Trampoline.ofResult
        match! TypeSet.isSubset types.system l u |> Trampoline.ofResult with
        | true ->
            let location = c1.trivia @ c2.trivia
            return UnionConstraint(l, u) |> Constraints.makeWithLocation location

        | false ->
            return! ConstraintMismatch(c1, c2) |> unifyError

    | UnionConstraint(l1, u1), InterfaceConstraint _ -> return! unifyTagSpaceAndInterfaceConstraint env env1 env2 c1 (l1, u1) (c2, r2, t2)
    | InterfaceConstraint _, UnionConstraint(l2, u2) -> return! unifyTagSpaceAndInterfaceConstraint env env2 env1 c2 (l2, u2) (c1, r1, t1)

    | InterfaceConstraint _, MultiElementTypeConstraint _
    | UnionConstraint _, MultiElementTypeConstraint _
    | MultiElementTypeConstraint _, (InterfaceConstraint _ | UnionConstraint _)
        -> return! unifyError(ConstraintMismatch(c1, c2))
}
let unifyInterfaceConstraint types env1 env2 (c1, fs1) (c2, fs2) = context {
    let rec aux fs kts2 = context {
        match kts2 with
        | [] -> return fs
        | (k2, t2)::kts2 ->

        match Map.tryFind k2 fs with
        | ValueNone -> return! aux (Map.add k2 t2 fs) kts2
        | ValueSome t1 ->
            do! unify types env1 env2 t1 t2
            return! aux fs kts2
    }
    let! fs =
        fs2
        |> Map.toList
        |> aux fs1

    return
        InterfaceConstraint fs
        |> Constraints.makeWithLocation (c1.trivia @ c2.trivia)
}
let unifyTagSpaceAndInterfaceConstraint ({ types = types } as env) env1 env2 c1 (l1, _) (c2, r2, t2) = context {
    match types.stringTableTypes with
    | [] -> return! unifyError(ConstraintMismatch(c1, c2))
    | _::_ ->

    let stringType = TypeSet [Type.makeWithEmptyLocation types.system.string]
    match TypeSet.isSubset types.system l1 stringType with
    | Error _
    | Ok false -> return! unifyError <| ConstraintMismatch(c1, c2)
    | Ok true ->

    // `("a").upper`
    // "a": ?x: "a"..
    // unify (?x: "a"..) (?y: { upper: ?z })
    // = unifyConstraints ("a"..) { upper: ?z }
    //     = matchConstraints { upper: fun(string) -> string, … } { upper: ?z }
    //     // ?z := fun(string) -> string
    // = "a"..string
    // // ?x := "a"..string
    // // ?y := "a"..string
    let rec aux ts = context {
        match ts with
        | [] ->
            let location = c1.trivia @ c2.trivia
            return
                UnionConstraint(l1, stringType)
                |> Constraints.makeWithLocation location

        | stringTableType::ts ->
            do! matchConstraints env env2 env1 (c2, r2, t2) stringTableType
            return! aux ts
    }
    return! aux types.stringTableTypes
}
let matchConstraints ({ types = types } as env) env1 env2 (c1, r1, t1) t2 = context {
    if Constraints.isAny c1 then return () else

    match c1.kind, t2.kind with

    // インターフェース型と型制約を単一化する
    // { … } :> { … }
    | InterfaceConstraint cfs, InterfaceType fs ->

        // インターフェース制約をチェック
        let rec aux (cfs: KeyValuePair<_,_> IEnumerator) = context {
            if not <| cfs.MoveNext() then cfs.Dispose(); return () else

            let ckt = cfs.Current
            match Map.tryFind ckt.Key fs with

            // フィールドが両方に存在するなら単一化
            // unify (?a: { x: ?ax }) { x: ?x } = unify ?ax ?x
            | ValueSome t ->
                do! unify env env1 env2 ckt.Value t
                return! aux cfs

            // フィールドが型制約のみに存在するならエラー
            // unify (?a: { x: number, y: number }) { x: number } = Some(RequireField "y")
            | _ -> return! unifyError(RequireField(fs, ckt.Key, ckt.Value))
        }

        return! aux <| (cfs :> _ seq).GetEnumerator()

    // number :> { f: t }
    | InterfaceConstraint cfs, NamedType(c, ts) ->
        match ts, types.stringTableTypes with

        // string :> { byte: …, char: … }
        | [], _::_ when c = types.system.stringConstant ->
            let rec aux ts = context {
                match ts with
                | [] -> return ()
                | stringTableType::ts ->

                do! matchConstraints env env1 env2 (c1, r1, t1) stringTableType
                return! aux ts
            }
            return! aux types.stringTableTypes

        | _ ->

        // unify number (?a: { x: number }) = Some(TypeMismatch ...)
        if Constraints.hasField c1 then
            let kv = Seq.head cfs
            return! unifyError(UndefinedField(t2, kv.Key))
        else

        return ()

    | UnionConstraint(lowerBound = lb; upperBound = ub), NamedType _ ->
        let space = TypeSet [t2]
        match TypeSet.isSubset types.system lb space, TypeSet.isSubset types.system space ub with
        | Ok true, Ok true -> return ()
        | _ ->
            return!
                ConstraintAndTypeMismatch(c1, t2)
                |> unifyError

    // unify (?t1...ce) ()
    | MultiElementTypeConstraint _, Type.IsEmpty types true -> return ()

    // unify (?c...ce) (?mt, mm...) = unify ?ce ?mt && unify (?c...ce) mm...
    | MultiElementTypeConstraint ce, Type.Cons types (ValueSome(mt, mm)) ->
        do! unify env env1 env2 ce mt
        let env1 = { env1 with visitedVarToType = Assoc.remove r1 env1.visitedVarToType }
        return! unify env env1 env2 t1 mm
    | _ ->
        return! unifyError(ConstraintAndTypeMismatch(c1, t2))
}
let unifyAbstractionAndType env env1 env2 typeAbstraction1 t2 =
    let struct(_, t1) = Scheme.instantiate 100000 typeAbstraction1
    unify env env1 env2 t1 t2

module Scheme =
    let ofType t = t

    let generalizeTypeParameterConstraints vps =
        let env = {
            visitedVars = []
            other = vps
        }
        vps
        |> List.map (fun struct(_, TypeParameter(n, p, c)) ->

            // 型制約の中の型も汎用化する
            let c =
                match c.kind with
                | InterfaceConstraint fs ->
                    if Map.isEmpty fs then c else
                    fs
                    |> Map.map (fun _ t -> Type.apply env t)
                    |> InterfaceConstraint
                    |> Constraints.makeWithLocation c.trivia

                | MultiElementTypeConstraint e ->
                    Type.apply env e
                    |> MultiElementTypeConstraint
                    |> Constraints.makeWithLocation c.trivia

                | UnionConstraint(lower, upper) ->
                    let lower = TypeSet.map (Type.apply env) lower
                    let upper = TypeSet.map (Type.apply env) upper
                    UnionConstraint(lower, upper)
                    |> Constraints.makeWithLocation c.trivia

            TypeParameter(n, p, c)
        )

    let createTypeParameters vs =
        vs
        |> List.map (fun struct(v, c) ->
            let p = TypeParameter.createNextWith v.varDisplayName v.varKind c
            struct(v, p)
        )

    let createAbstraction vars ps t =
        let t = Type.apply vars t
        match ps with
        | [] -> t
        | _ ->

        match t with
        | { kind = TypeAbstraction(ps', et) } -> TypeAbstraction(ps@ps', et) |> Type.withEntity t
        | _ -> TypeAbstraction(ps, t) |> Type.withEntity t

    let generalizeAndAssign level t =
        match Type.freeVars level t with
        | [] -> Type.apply { visitedVars = []; other = [] } t
        | vars ->

        let vars = createTypeParameters vars
        let ps = generalizeTypeParameterConstraints vars

        // 汎用化された型引数で型変数を置き換える
        // 例：
        // 元の型 `(?a: { x: ?b }) -> (?r := ?a)` から
        // 汎用化された型 `type ('0: { x: '1 }) '1. '0 -> '0` を得る
        // その型引数を元の型に代入すると
        // 元の型は `(?a := '0) -> (?r := '0)` になる
        Type.assign vars t
        let vars = {
            visitedVars = []
            other = vars
        }
        createAbstraction vars ps t

    let generalize level t =
        match Type.freeVars level t with
        | [] -> Type.apply { visitedVars = []; other = [] } t
        | vars ->

        let vars = createTypeParameters vars
        let ps = generalizeTypeParameterConstraints vars
        let vars = {
            visitedVars = []
            other = vars
        }
        createAbstraction vars ps t

    let takeHeadParameters ps t =
        match t.kind with
        | TypeAbstraction([], t) -> takeHeadParameters ps t
        | TypeAbstraction(ps', t) -> takeHeadParameters (ps @ ps') t
        | VarType { target = Assigned t } -> takeHeadParameters ps t
        | _ -> struct(ps, t)

    let instantiate level t =
        let struct(ps, t) = takeHeadParameters [] t
        match ps with
        | [] -> struct([], t)
        | _ ->

        // `type ('0: { x: '1 }) '1. '0` のような型の場合
        // pvs = [?0, { x: '1 }; ?1, _]
        let pvs =
            ps
            |> List.map (fun (TypeParameter(n, TypeParameterId(_, k), _) as p) ->
                struct(p, Var.newVar n level k)
            )
        // vs = [?0; ?1]
        let vs =
            pvs
            |> List.map (fun struct(TypeParameter(_, p, _), v) ->
                struct(p, Type.makeWithEmptyLocation(VarType v))
            )

        let env = {
            visitedVars = []
            other = vs
        }
        for TypeParameter(_, _, c), v in pvs do
            let c =
                match c.kind with
                | InterfaceConstraint fs ->
                    if Map.isEmpty fs then c else

                    fs
                    |> Map.map (fun _ t -> Type.instantiate' env t)
                    |> InterfaceConstraint
                    |> Constraints.makeWithLocation c.trivia

                | MultiElementTypeConstraint t ->
                    t
                    |> Type.instantiate' env
                    |> MultiElementTypeConstraint
                    |> Constraints.makeWithLocation c.trivia

                | UnionConstraint(lower, upper) ->
                    let lower = TypeSet.map (Type.instantiate' env) lower
                    let upper = TypeSet.map (Type.instantiate' env) upper
                    UnionConstraint(lower, upper)
                    |> Constraints.makeWithLocation c.trivia

            v.target <- Var(level, c)

        // vs = [(?0: { x: ?1 }); ?1]
        struct(vs, Type.instantiate' env t)
        // result = (?0: { x: ?1 })

module TypeSystem =
    let multi1 types t location = types.cons(t, Type.makeWithLocation location types.empty) |> Type.makeWithLocation location
