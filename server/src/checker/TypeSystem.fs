[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module rec LuaChecker.TypeSystem
open Cysharp.Text
open System.Collections.Generic
open System.Threading
module S = Syntaxes


module TypeParameterId =
    let private nextId = ref 0L
    let createNext kind = TypeParameterId(Interlocked.Increment &nextId.contents, kind)

module TypeParameter =
    let createNextWith displayName kind constraints = TypeParameter(displayName, TypeParameterId.createNext kind, constraints)
    let createNext displayName kind = createNextWith displayName kind Constraints.any

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
    let any = InterfaceConstraint Map.empty |> makeWithEmptyLocation

    let isAny c = InternalConstraints.isAny c
    let hasField = function
        | { kind = InterfaceConstraint fs } -> Map.isEmpty fs |> not
        | _ -> false

    let ofInterfaceType fields = InterfaceConstraint fields
    /// v..
    let literal1 v = TagSpaceConstraint(lowerBound = TagSpace.ofLiteral v, upperBound = TagSpace.full)
    let freeVars' level vars c =
        match c.kind with
        | InterfaceConstraint fs -> Map.fold (fun vars _ t -> Type.freeVars' level vars t) vars fs
        | MultiElementTypeConstraint t -> Type.freeVars' level vars t
        | TagSpaceConstraint _ -> vars

    let apply vs c =
        match c.kind with
        | InterfaceConstraint fs ->
            Map.map (fun _ t -> Type.apply vs t) fs |> InterfaceConstraint

        | MultiElementTypeConstraint t ->
            Type.apply vs t |> MultiElementTypeConstraint

        | TagSpaceConstraint _ as t -> t

        |> withEntity c

    let instantiate' vs c =
        match c.kind with
        | InterfaceConstraint fs ->
            Map.map (fun _ t -> Type.instantiate' vs t) fs |> InterfaceConstraint

        | MultiElementTypeConstraint t ->
            Type.instantiate' vs t |> MultiElementTypeConstraint

        | TagSpaceConstraint _ as t -> t

        |> withEntity c

    let show c =
        use mutable b = ZString.CreateStringBuilder()
        let mutable state = TypePrintState.create TypeWriteOptions.Default
        let scope = TypePrintScope.empty
        ConstraintsExtensions.AppendConstraints(&b, c, &scope, &state)
        b.ToString()

module Kind =
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
type UnifyEnv = {
    visitedVarToType: Assoc<VarTypeSite, Type>
}
module UnifyEnv =
    let empty = {
        visitedVarToType = Assoc.empty
    }

let containsVar v = function
    | [] -> false
    | v'::vs -> VarType.physicalEquality v' v || containsVar v vs

let addVar v env =
    if containsVar v env.visitedVars then ValueNone else
    ValueSome { env with visitedVars = v::env.visitedVars }

[<Struct>]
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

    let newVarWith displayName level kind c = VarType { target = Var(level, c); varKind = kind; varDisplayName = displayName }
    let newVar displayName level kind = newVarWith displayName level kind Constraints.any

    let freeVars' env vars t =
        match t.kind with
        | NamedType(_, []) -> vars
        | NamedType(_, ts) -> List.fold (freeVars' env) vars ts
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
                | TagSpaceConstraint _ -> ()

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

    let unify types t1 t2 = TypeSystem.unify types UnifyEnv.empty UnifyEnv.empty t1 t2
    let kind types t =
        match t.kind with
        | NamedType(TypeConstant(_, k), _) ->
            match k with
            | NamedKind _ -> k
            | FunKind(_, k) -> k

        | InterfaceType _ -> types.system.valueKind
        | TypeAbstraction(_, t) -> kind types t
        | ParameterType(TypeParameterId(_, k))
        | VarType { varKind = k } -> k

module MultiType =
    let minLength types m =
        let rec multi visited min m =
            match m.kind with
            | Type.IsEmpty types true -> min
            | Type.Cons types (ValueSome(_, m)) -> multi visited (min + 1) m
            | Type.MultiVar types (ValueSome r) ->
                if containsVar r visited then min else
                let visited = r::visited

                match r.target with
                | Assigned m -> multi visited min m
                | Var(_, c) -> constraints min c

            | Type.MultiParameter types (ValueSome _) -> min

            // without multi kind
            | _ -> min

        and constraints min = function

            // `?m...number`
            | { kind = MultiElementTypeConstraint _ } -> min

            // `?m...` `?m...: { k: t, … }`
            | _ -> min

        multi [] 0 m

let occur env r t =
    match t.kind with
    | VarType r' ->
        if VarType.physicalEquality r' r then true else
        match addVar r' env with
        | ValueNone -> false
        | ValueSome env ->

        match r'.target with
        | Var _  -> adjustVarLevel r r'; false
        | Assigned t -> occur env r t

    | NamedType(_, ts) -> List.exists (occur env r) ts
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
            | TagSpaceConstraint _ -> false
        ) ps ||
        occur env r t

type UnifyError =
    | TypeMismatch of Type * Type
    | RequireField of actualFields: Map<FieldKey, Type> * requireKey: FieldKey * requireType: Type
    | UndefinedField of selfType: Type * fieldKey: FieldKey
    | KindMismatch of Kind * Kind
    | ConstraintMismatch of Constraints * Constraints
    | ConstraintAndTypeMismatch of Constraints * Type
    | TagSpaceConstraintMismatch of expectedLowerBound: TagSpace * expectedUpperBound: TagSpace * actualType: Type * requireElement: TagElement

let unifyKindList (all1, all2) (ks1, ks2) =
    let rec aux = function
        | [], [] -> ValueNone
        | k1::ks1, k2::ks2 ->
            match unifyKind k1 k2 with
            | ValueSome _ as r -> r
            | _ -> aux (ks1, ks2)
        | _ ->
            ValueSome(KindMismatch(all1, all2))

    aux (ks1, ks2)

let unifyKind k1 k2 =
    match k1, k2 with
    | NamedKind n1, NamedKind n2 when n1 = n2 -> ValueNone

    | (FunKind(ks1, k1) as kind1), (FunKind(ks2, k2) as kind2) ->
        match unifyKindList (kind1, kind2) (ks1, ks2) with
        | ValueSome _ as r -> r
        | _ -> unifyKind k1 k2

    | _ -> ValueSome(KindMismatch(k1, k2))

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

let unifyList types env1 env2 all1 all2 ts1 ts2 =
    match ts1, ts2 with
    | [], [] -> ValueNone
    | t1::ts1, t2::ts2 ->
        match unify types env1 env2 t1 t2 with
        | ValueSome _ as r -> r
        | _ -> unifyList types env1 env2 all1 all2 ts1 ts2

    | _ -> ValueSome(TypeMismatch(all1, all2))

let unifyMap types env1 env2 all1 all2 (e1: IEnumerator<KeyValuePair<FieldKey, Type>> byref) (e2: IEnumerator<KeyValuePair<FieldKey, Type>> byref) =
    match e1.MoveNext(), e2.MoveNext() with
    | false, false -> ValueNone
    | true, true ->
        let kv1 = e1.Current
        let kv2 = e2.Current
        if kv1.Key <> kv2.Key then ValueSome <| missingFieldError all1 all2 else

        match unify types env1 env2 kv1.Value kv2.Value with
        | ValueSome _ as r -> r
        | _ -> unifyMap types env1 env2 all1 all2 &e1 &e2

    | _ -> ValueSome <| missingFieldError all1 all2

let unify types env1 env2 t1 t2 =
    match t1.kind, t2.kind with
    | NamedType(n1, ts1), NamedType(n2, ts2) ->
        if n1 <> n2 then ValueSome(TypeMismatch(t1, t2)) else

        match ts1, ts2 with
        | [], [] -> ValueNone
        | _ -> unifyList types env1 env2 t1 t2 ts1 ts2

    | InterfaceType fs1, InterfaceType fs2 ->
        if Map.count fs1 <> Map.count fs2 then ValueSome <| missingFieldError fs1 fs2 else

        let mutable e1 = (fs1 :> _ seq).GetEnumerator()
        let mutable e2 = (fs2 :> _ seq).GetEnumerator()
        unifyMap types env1 env2 fs1 fs2 &e1 &e2

    | ParameterType p1, ParameterType p2 ->
        if p1 = p2 then ValueNone else
        ValueSome(TypeMismatch(t1, t2))

    // unify ?a ?a = []
    // unify (?a := x) (?a := x) = []
    | VarType r1, VarType r2 when LanguagePrimitives.PhysicalEquality r1 r2 -> ValueNone

    // unify (?x := a) x
    | VarType({ target = Assigned at1 } as r1), _ -> unifyAssignedTypeAndType types env1 env2 (at1, r1, t1) t2
    | _, VarType({ target = Assigned at2 } as r2) -> unifyAssignedTypeAndType types env2 env1 (at2, r2, t2) t1

    | TypeAbstraction([], t1), _ -> unify types env1 env2 t1 t2
    | _, TypeAbstraction([], t2) -> unify types env1 env2 t1 t2

    | VarType({ target = Var(l1, c1) } as r1), _ -> unifyVarAndType types env1 env2 (l1, c1, r1, t1) t2
    | _, VarType({ target = Var(l2, c2) } as r2) -> unifyVarAndType types env2 env1 (l2, c2, r2, t2) t1

    // TODO:
    | TypeAbstraction(TypeParameter(_, TypeParameterId(id1, _), _)::_, _),
        TypeAbstraction(TypeParameter(_, TypeParameterId(id2, _), _)::_, _) when id1 = id2 -> ValueNone

    | TypeAbstraction _, _ -> unifyAbstractionAndType types env1 env2 t1 t2
    | _, TypeAbstraction _ -> unifyAbstractionAndType types env2 env1 t2 t1

    | _ -> ValueSome(TypeMismatch(t1, t2))

let unifyAssignedTypeAndType types env1 env2 (at1, r1, t1) t2 =
    match Assoc.tryFind r1 env1.visitedVarToType with

    // unify (?t1 :=(not rec) at1) t2 = unify at1 t2
    | ValueNone ->
        let env1 = { env1 with visitedVarToType = Assoc.add r1 t2 env1.visitedVarToType }
        unify types env1 env2 at1 t2

    // unify (?t1 :=(rec(?fr2)) at1) t2
    | ValueSome { kind = VarType({ target = Assigned _ } as fr2) } ->

        match t2.kind with
        | VarType({ target = Assigned at2 } as r2) ->

            // unify (?t1 :=(rec(?fr2)) at1) ?fr2 = Ok
            if VarType.physicalEquality fr2 r2 then ValueNone else

            match Assoc.tryFindBy VarType.physicalEquality r2 env2.visitedVarToType with

            // unify (?t1 :=(rec(?fr2)) at1) (?t2 =?(rec) at2) = Error occur
            | ValueSome _ -> ValueSome(TypeMismatch(t1, t2))

            // unify (?t1 :=(rec(?fr2)) at1) (?t2 =?(not rec) at2) = unify at1 at2
            | _ ->
                let env2 = { env2 with visitedVarToType = Assoc.add r2 t1 env2.visitedVarToType }
                unify types env1 env2 at1 at2

        // unify (?t1 :=(rec(?fr2)) at1) t2 = unify at1 t2
        | _ ->
            unify types env1 env2 at1 t2

    // unify (?t1 :=(rec(ft2)) at1) t2
    | ValueSome _ -> unify types env1 env2 at1 t2

let tryAddVisitedVar env1 (r1, c1) t2 =
    match Assoc.tryFindBy VarType.physicalEquality r1 env1.visitedVarToType with

    // unify [?t1,f2] (?t1: … ?t1 …)
    | ValueSome f2 -> Error f2
    | _ ->

    // 循環するのは制約付き型変数のみ
    if Constraints.isAny c1 then Ok env1

    else Ok { env1 with visitedVarToType = Assoc.add r1 t2 env1.visitedVarToType }

let unifyVarAndType types env1 env2 (_, c1, r1, t1) t2 =
    occur TypeVisitEnv.empty r1 t2 |> ignore

    match t2.kind with
    | VarType({ target = Assigned at2 } as r2) -> unifyAssignedTypeAndType types env2 env1 (at2, r2, t2) t1
    | VarType({ target = Var(l2, c2) } as r2) ->

        // c1 内を探索するので循環チェックが必要
        match tryAddVisitedVar env1 (r1, c1) t2 with
        | Error _ ->
            // TODO:
            ValueNone

        | Ok env1 ->

        match unifyKind r1.varKind r2.varKind with
        | ValueSome _ as r -> r
        | _ ->

        let f1, env2 =
            match Assoc.tryFindBy VarType.physicalEquality r2 env2.visitedVarToType with
            | ValueSome _ as f1 -> f1, env2
            | f1 -> f1, { env2 with visitedVarToType = Assoc.add r2 t1 env2.visitedVarToType }

        match unifyConstraints types env1 env2 c1 c2 with
        | Error e -> ValueSome e
        | Ok c ->

        // unify (?t1: c1) (?t2: c2) = [?t3: unify c1 c2; ?t1 := ?t3; ?t2 := ?t3]
        let location3 = t1.trivia @ t2.trivia
        let t3 = Type.newVarWith "" l2 r2.varKind c |> Type.makeWithLocation location3
        r2.target <- Assigned t3
        r1.target <- Assigned t3

        match f1 with
        | ValueSome { kind = TypeAbstraction _ } ->
            // TODO:
            ValueNone

        | ValueSome f1 -> unify types env1 env2 f1 t2
        | _ -> ValueNone

    | InterfaceType _
    | NamedType _ ->

        // c1 内を探索するので循環チェックが必要
        match tryAddVisitedVar env1 (r1, c1) t2 with
        | Error _ -> ValueSome(TypeMismatch(t1, t2))
        | Ok env1 ->

        match unifyKind r1.varKind (Type.kind types t2) with
        | ValueSome _ as r -> r
        | _ ->

        match matchConstraints types env1 env2 (c1, r1, t1) t2 with
        | ValueSome _ as e -> e
        | _ ->

        // f: type ('t: { x: number }). ('t, 't) -> 't
        // f({ x = 10, y = 20 }, { x = 10 })
        //
        // [generalize] f: (?a, ?a) -> (?a: { x: number })
        // [unify] (?a: { x: number }) { x: number, y: number } => [?a = { x: number, y: number }]
        // [unify] (?a := { x: number, y: number }) { x: number } = Some(RequireField("y"))
        r1.target <- Assigned t2
        ValueNone

    // unify ?v 'a
    | ParameterType _ ->
        // TODO:
        ValueSome(TypeMismatch(t1, t2))

    // unify ?v (type 'a. t)
    | TypeAbstraction _ ->
        // ここでは直接 c1 内を探索しないので循環チェック不要
        unifyAbstractionAndType types env2 env1 t2 t1

// unify ('a: { f: ?af }) ('b: { f: ?bf; g: ?bg }) = unify ?af ?bf @ ['a = 'b; 'a: { f: ?af, g: ?bg }]
// unify ('a: { f: ?af }) { f: ?f } = unify ?af ?f @ ['a = { f: ?af }]
// unify 'a t = ['a = t]
let unifyConstraints types env1 env2 c1 c2 =
    if Constraints.isAny c1 then Ok c2 else
    if Constraints.isAny c2 then Ok c1 else

    match c1.kind, c2.kind with
    | InterfaceConstraint fs1, InterfaceConstraint fs2 ->
        unifyInterfaceConstraint types env1 env2 (c1, fs1) (c2, fs2)

    | MultiElementTypeConstraint e1, MultiElementTypeConstraint e2 ->
        match unify types env1 env2 e1 e2 with
        | ValueSome e -> Error e
        | _ -> Ok c1

    | TagSpaceConstraint(l1, u1), TagSpaceConstraint(l2, u2) ->
        if l1 = l2 && u1 = u2 then Ok c1 else

        // unify
        //     ( ( 1 | 'a' )..( 1 | 2 | 3 | 4 | 'a' | 'b' ) )
        //     ( ( 1 | 2 | 3 | 'x' )..( 1 | 2 | 3 | 4 | 5 | 'x' | 'y' ) )
        // = ( ( 1 | 2 | 3 | 'a' | 'x' )..( 1 | 2 | 3 | 4 ) )
        // = Error
        let l = TagSpace.union l1 l2
        let u = TagSpace.intersect u1 u2
        if TagSpace.isSubset l u
        then
            let location = c1.trivia @ c2.trivia
            TagSpaceConstraint(l, u) |> Constraints.makeWithLocation location |> Ok
        else
            ConstraintMismatch(c1, c2) |> Error

    | InterfaceConstraint _, (MultiElementTypeConstraint _ | TagSpaceConstraint _)
    | MultiElementTypeConstraint _, (InterfaceConstraint _ | TagSpaceConstraint _)
    | TagSpaceConstraint _, (InterfaceConstraint _ | MultiElementTypeConstraint _)
        -> Error(ConstraintMismatch(c1, c2))

let unifyInterfaceConstraint types env1 env2 (c1, fs1) (c2, fs2) =
    let rec aux fs = function
        | [] -> Ok fs
        | (k2, t2)::kts2 ->

        match Map.tryFind k2 fs with
        | ValueNone -> aux (Map.add k2 t2 fs) kts2
        | ValueSome t1 ->
            match unify types env1 env2 t1 t2 with
            | ValueSome e -> Error e
            | _ -> aux fs kts2

    let fs =
        fs2
        |> Map.toList
        |> aux fs1

    match fs with
    | Error e -> Error e
    | Ok fs ->

    InterfaceConstraint fs
    |> Constraints.makeWithLocation (c1.trivia @ c2.trivia)
    |> Ok

let typeToSpace { system = types } = function
    | { kind = NamedType(t, _) } ->
        if t = types.nilConstant then ValueSome TagSpace.nil
        elif t = types.booleanConstant then ValueSome TagSpace.allBoolean
        elif t = types.numberConstant then ValueSome TagSpace.allNumber
        elif t = types.stringConstant then ValueSome TagSpace.allString
        elif t = types.fnConstant then ValueSome TagSpace.allFunction
        elif t = types.tableConstant then ValueSome TagSpace.allTable
        elif t = types.threadConstant then ValueSome TagSpace.allThread
        else ValueNone

    | _ -> ValueNone

let matchConstraints types env1 env2 (c1, r1, t1) t2 =
    if Constraints.isAny c1 then ValueNone else

    match c1.kind, t2.kind with

    // インターフェース型と型制約を単一化する
    // { … } :> { … }
    | InterfaceConstraint cfs, InterfaceType fs ->

        // インターフェース制約をチェック
        cfs
        |> Seq.tryPickV (fun ckt ->
            match Map.tryFind ckt.Key fs with

            // フィールドが両方に存在するなら単一化
            // unify (?a: { x: ?ax }) { x: ?x } = unify ?ax ?x
            | ValueSome t -> unify types env1 env2 ckt.Value t

            // フィールドが型制約のみに存在するならエラー
            // unify (?a: { x: number, y: number }) { x: number } = Some(RequireField "y")
            | _ -> ValueSome(RequireField(fs, ckt.Key, ckt.Value))
        )

    // number :> { f: t }
    | InterfaceConstraint cfs, NamedType(c, ts) ->
        match ts, types.stringTableTypes with

        // string :> { byte: …, char: … }
        | [], _::_ when c = types.system.stringConstant ->
            let rec aux = function
                | [] -> ValueNone
                | stringTableType::ts ->

                match matchConstraints types env1 env2 (c1, r1, t1) stringTableType with
                | ValueNone -> aux ts
                | r -> r

            aux types.stringTableTypes

        | _ ->

        // unify number (?a: { x: number }) = Some(TypeMismatch ...)
        if Constraints.hasField c1 then
            let kv = Seq.head cfs
            ValueSome(UndefinedField(t2, kv.Key))
        else

        ValueNone

    | TagSpaceConstraint(lowerBound = lb; upperBound = ub), NamedType _ ->
        match typeToSpace types t2 with
        | ValueSome space ->
            if TagSpace.isSubset lb space && TagSpace.isSubset space ub then
                ValueNone
            else
                let e =
                    match TagSpace.difference1 lb space with
                    | ValueSome e -> e
                    | _ -> TagSpace.difference1 space ub |> ValueOption.defaultValue TagElement.AllThread

                TagSpaceConstraintMismatch(
                    expectedLowerBound = lb,
                    expectedUpperBound = ub,
                    actualType = t2,
                    requireElement = e
                )
                |> ValueSome

        | _-> ValueSome <| ConstraintAndTypeMismatch(c1, t2)

    // unify (?t1...ce) ()
    | MultiElementTypeConstraint _, Type.IsEmpty types true -> ValueNone

    // unify (?c...ce) (?mt, mm...) = unify ?ce ?mt && unify (?c...ce) mm...
    | MultiElementTypeConstraint ce, Type.Cons types (ValueSome(mt, mm)) ->
        match unify types env1 env2 ce mt with
        | ValueSome _ as r -> r
        | _ ->
            let env1 = { env1 with visitedVarToType = Assoc.remove r1 env1.visitedVarToType }
            unify types env1 env2 t1 mm
    | _ ->
        ValueSome(ConstraintAndTypeMismatch(c1, t2))

let unifyAbstractionAndType types env1 env2 typeAbstraction1 t2 =
    let struct(_, t1) = Scheme.instantiate 100000 typeAbstraction1
    unify types env1 env2 t1 t2

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

                | TagSpaceConstraint _ -> c

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
                struct(p, { target = Var(level, Constraints.any); varKind = k; varDisplayName = n })
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

                | TagSpaceConstraint _ -> c

            v.target <- Var(level, c)

        // vs = [(?0: { x: ?1 }); ?1]
        struct(vs, Type.instantiate' env t)
        // result = (?0: { x: ?1 })

module TypeSystem =
    let multi1 types t location = types.cons(t, Type.makeWithLocation location types.empty) |> Type.makeWithLocation location
