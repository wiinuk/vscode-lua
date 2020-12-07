module LuaChecker.TypeSystem.Tests
open Xunit
open LuaChecker
open LuaChecker.Checker.Test.Utils
open LuaChecker.Checker.Test.TypeExtensions
open LuaChecker.Checker.Test.Helpers
open LuaChecker.Syntax
module T = TypedSyntaxes
module C = Constraints


[<Fact>]
let unifyVarAndNumber() =
    let t1 = Type.newVar 1
    unify t1 types.number =? ValueNone
    Scheme.normalize t1 =? type0 types.number

[<Fact>]
let unifyVarAndVar() =
    // unify 'a 'b = ['a = 'b]
    let a = Type.newVar 1
    let b = Type.newVar 1
    unify a b =? ValueNone
    ([a; b] ->. []) |> Scheme.normalize =? type1 (fun a -> [a; a] ->. [])

[<Fact>]
let unifyVarWithInterfaceAndInterface() =
    // unify ('a: { x: number }) { x: string }
    let a = Type.newVarWithFields 1 ["x", types.number]
    let i = Type.interfaceType ["x", types.string]
    unify a i =? ValueSome(TypeMismatch((types.number, types.string)))

[<Fact>]
let unifyVarWithInterfaceAndVarWithInterface() =
    // unify ('a: { x: number, y: 'ay }) ('b: { x: 'bx, y: string, z: 'bz }) =>
    // type ('t0: { x: number, y: string, z: 't1 }) 't1. ('t0, 't0, string, number, 't1)
    let ay = Type.newVar 1
    let bx = Type.newVar 1
    let bz = Type.newVar 1
    let a = Type.newVarWithFields 1 ["x", types.number; "y", ay]
    let b = Type.newVarWithFields 1 ["x", bx; "y", types.string; "z", bz]
    unify a b =? ValueNone

    [a; b; ay; bx; bz] ->. []
    |> Scheme.normalize
    =? forall2 (fun t0 t1 ->
        (Constraints.ofFields ["x", types.number; "y", types.string; "z", t1], Constraints.any),
        [t0; t0; types.string; types.number; t1] ->. []
    )

[<Fact>]
let multi2VarSchemeRoundTrip() =
    // type 'a. fun('a, 'a): ()
    let t = type1 (fun a -> [a; a] ->. [])
    let struct(_, t) = t |> Scheme.instantiate 1 in t |> Scheme.normalize =? type1 (fun a -> [a; a] ->. [])

[<Fact>]
let unifyVarAndInterface() =
    // unify (?a: { x: number }) { x: ?x } => [?a = { x: ?x }; ?x = number]
    let t1 = Type.newVarWithFields 1 ["x", types.number]
    let t2 = Type.interfaceType ["x", Type.newVar 1]
    unify t1 t2 =? ValueNone
    [t1; t2] ->. [] |> Scheme.normalize
        =?
        let t = Type.interfaceType ["x", types.number]
        type0 ([t; t] ->. [])

[<Fact>]
let unifyNumberAndVarWithInterface() =
    // unify number (?a: { x: number }) =? error
    let t1 = types.number
    let t2 = Type.newVarWithFields 1 ["x", types.number]
    unify t1 t2 =? ValueSome(UndefinedField(t1, FieldKey.String "x"))

[<Fact>]
let syntaxHitTest() =
    let visitor = {
        literal = fun struct(_, x) -> x.trivia.span, TokenKind.ofLiteralKind x.kind
        name = fun struct(_, Name x) -> x.trivia.span, TokenKind.Name x.kind
        reserved = fun struct(_, t, k) -> t.span, k
    }
    let test i source =
        let s = Scanner.create source
        match Parser.block s with
        | Error e -> failwithf "%A" e
        | Ok x -> Block.hitTest visitor () i x

    let token (s, e) k = ValueSome({ start = s; end' = e }, k)

    let source = "local function f() return end"
    test -1 source =? ValueNone
    test 0 source =? token (0, 5) TokenKind.Local
    test 4 source =? token (0, 5) TokenKind.Local
    test 5 source =? ValueNone
    test 6 source =? token (6, 14) TokenKind.Function
    test 15 source =? token (15, 16) (TokenKind.Name "f")
    test 16 source =? token (16, 17) TokenKind.LBracket
    test 17 source =? token (17, 18) TokenKind.RBracket
    test 19 source =? token (19, 25) TokenKind.Return
    test 26 source =? token (26, 29) TokenKind.End
    test 29 source =? ValueNone
    test 30 source =? ValueNone

[<Fact>]
let typedHitTest() =
    let normalize _ t = Type.apply { visitedVars = []; other = [] } t |> Scheme.normalize
    let getNormalizedType t _ _ = normalize () t

    let visitor = {
        var = fun struct(_, T.Var(Name n, t, l), e) ->
            TokenKind.Name n.kind, n.trivia.span, getNormalizedType t l e
        reserved = fun struct(_, T.ReservedVar(s, k, t, l), e) -> k, s.span, getNormalizedType t l e
        literal = fun struct(_, x, t, _, _) -> TokenKind.ofLiteralKind x.kind, x.trivia.span, normalize 0 <| Scheme.normalize t
        typeTag = fun struct(_, s, t, _) -> TokenKind.Unknown, s.trivia, Scheme.normalize t
    }
    let test i source =
        match checkChunk id source with
        | Some s, [] -> LuaChecker.Block.hitTest visitor () i s.entity
        | _, es -> failwithf "%A" <| Seq.toList es

    let typed (start, end') kind type' =
        ValueSome(kind, { start = start; end' = end' }, Scheme.ofType type')

    let source = "local function add10(a) return a + 10 end"
    test 0 source =? ValueNone
    test 15 source =? typed (15, 20) (TokenKind.Name "add10") ([types.number] ->. [types.number])
    test 19 source =? typed (15, 20) (TokenKind.Name "add10") ([types.number] ->. [types.number])
    test 20 source =? ValueNone
    test 21 source =? typed (21, 22) (TokenKind.Name "a") types.number
    test 31 source =? typed (31, 32) (TokenKind.Name "a") types.number
    test 33 source =? typed (33, 34) TokenKind.Add ([types.number; types.number] ->. [types.number])
    test 35 source =? typed (35, 37) (TokenKind.Number 10.) types.number

[<Fact(DisplayName = "generalize (?a: { f: ?b }) = (type ('0: { f: '1 }) '1. '0)")>]
let generalizeInterfaceConstraints() =
    let b = Type.newVar 1
    let a = Type.newVarWithFields 1 ["f", b]

    Scheme.generalize 0 a
    |> Scheme.normalize
    =? forall2 (fun t0 t1 -> (Constraints.ofFields ["f", t1], Constraints.any), t0)

[<Fact(DisplayName = "generalize (fun(?m...?a): ()) = (type 'm...'a 'a. fun('m...): ())")>]
let generalizeMultiTypeVarConstraint() =
    let a = Type.newVar 1
    let t = types.fn(MultiType.newVarWith 1 (ValueSome(MultiElementTypeConstraint a |> withEmptyLocation)), types.empty)
    Scheme.generalize 0 t
    |> Scheme.normalize
    =?
    forall2With (types.multiKind, types.valueKind) (fun m a ->
        (MultiElementTypeConstraint a |> withEmptyLocation, Constraints.any), types.fn(m, types.empty)
    )

[<Fact>]
let generalizeWithLevel() =
    // generalize 0 `?a(1) -> ?b(0)` = `type '0. '0 -> ?b(0)`
    let a = Type.newVar 1
    let b = Type.newVar 0
    let t = [a] ->. [b]
    Scheme.normalize t =? type1 (fun t0 -> [t0] ->. [b])

[<Fact>]
let adjustLevel() =
    // unify `?a(0) -> string` `?b(1) -> string` => (?b := (0))
    let a = Type.newVar 0
    let b = Type.newVar 1
    let t1 = [a] ->. [types.string]
    let t2 = [b] ->. [types.string]
    unify t1 t2 =? ValueNone
    // ?b(1) -> int

    match b with
    | { kind = VarType { target = Assigned { kind = VarType { target = LuaChecker.Var(0, _) } } } } -> ()
    | b -> failwithf "%A" b

[<Fact(DisplayName = "instantiate `type(a) -> type(b) -> fun(a, b) -> ()` = `fun(?x, ?y) -> ()`")>]
let instantiateScheme2() =
    let type1 = type1With <| fun c -> { c with t = { c.t with normalize = id } }

    /// type a. type b. fun(a, b): ()
    let t0 = type1 <| fun t0 -> type1 <| fun t1 -> [t0; t1] ->. []

    /// type a b. fun(a, b): ()
    let t1 = type2 <| fun t1 t2 -> [t1; t2] ->. []

    let struct(_, t) = Scheme.instantiate 1 t0
    Scheme.normalize t =? t1

[<Fact(DisplayName = "instantiate `{ f: type a. fun(a): () }` = `{ f: type a. fun(a): () }`")>]
let instantiateSchemeField() =
    /// { f: type a. fun(a): () }
    let t0 = Type.interfaceType [
        "f", type1 <| fun t0 -> [t0] ->. []
    ]
    let struct(_, t) = Scheme.instantiate 1 t0
    Scheme.normalize t
    =?
    Scheme.normalize t0

[<Fact>]
let unifyRecursiveFunctionType() =
    /// ?f := fun(number): ?f
    let f() =
        let f = Type.newVar 1
        match f.kind with
        | VarType r -> r.target <- Assigned([types.number] ->. [f])
        | _ -> ()
        f

    /// ?x := fun(number): (fun(number): ?x)
    let x() =
        let x = Type.newVar 1
        match x.kind with
        | VarType r -> r.target <- Assigned([types.number] ->. [[types.number] ->. [x]])
        | _ -> ()
        x

    /// ?y := fun(number): (fun(string): ?y)
    let y() =
        let y = Type.newVar 1
        match y.kind with
        | VarType r -> r.target <- Assigned([types.number] ->. [[types.string] ->. [y]])
        | _ -> ()
        y

    unify (f()) (x()) =? ValueNone
    unify (f()) (y()) =? ValueSome(TypeMismatch(types.number, types.string))

[<Fact>]
let unifyRecursiveConstraint() =
    let xId = TypeParameterId.createNext types.valueKind
    let x = ParameterType xId |> Type.makeWithEmptyLocation

    /// 'x: { f: fun(number): 'x }
    let gt = TypeAbstraction([TypeParameter("", xId, Constraints.ofFields ["f", [types.number] ->. [x]])], x) |> Type.makeWithEmptyLocation
    let struct(_, t1) = Scheme.instantiate 0 gt
    let struct(_, t2) = Scheme.instantiate 0 gt

    // unify (?x: { f: fun(number): ?x }) (?y: { f: fun(number): ?y })
    unify t1 t2 =? ValueNone

[<Fact>]
let tagSpaceIsSubset() =
    let ofNumbers = TagSpace.ofNumbers

    TagSpace.isSubset (ofNumbers []) TagSpace.allNumber =? true
    TagSpace.isSubset (ofNumbers []) (ofNumbers []) =? true
    TagSpace.isSubset (ofNumbers []) (ofNumbers [1.]) =? true
    TagSpace.isSubset (ofNumbers [1.]) (ofNumbers []) =? false
    TagSpace.isSubset (ofNumbers [1.;2.]) (ofNumbers [1.;2.]) =? true
    TagSpace.isSubset (ofNumbers [1.]) (ofNumbers [1.;2.]) =? true
    TagSpace.isSubset (ofNumbers [1.;2.]) (ofNumbers [1.]) =? false
    TagSpace.isSubset (ofNumbers [1.;2.]) (ofNumbers [1.;3.]) =? false
    TagSpace.isSubset TagSpace.allNumber (ofNumbers []) =? false
    TagSpace.isSubset (ofNumbers [1.;2.]) TagSpace.allNumber =? true
    TagSpace.isSubset TagSpace.allNumber (ofNumbers [1.;2.]) =? false
    TagSpace.isSubset TagSpace.allNumber TagSpace.allNumber =? true

[<Fact>]
let unifyAbstractionAndTagSpaceConstraint() =
    // type(y) -> fun(y) -> { x: (?x(2): 1..); y: y; }
    let with1T =
        let x = Type.newValueVarWith 2 <| Constraints.numberOrUpper 1.
        type1 <| fun y -> [y] ->. [Type.interfaceType ["x", x; "y", y]]

    // ?a(2)
    let a = Type.newVar 2

    unify with1T a =? ValueNone

[<Fact>]
let stringTypeToTagSpace() =
    typeToSpace types' types.string =? ValueSome TagSpace.allString

[<Fact>]
let unifyStringSpaceConstraintInMulti() =
    let r = MultiType.newVar 1
    let r1 = multi [stringT "ok"]
    let r2 = multi [numberT 123.]
    unify r r1 =? ValueNone
    unify r r2 =? ValueNone

    Scheme.normalize r
    =?
    // type(a: ("ok" | 123)..) -> (a,)
    scheme1With (types.valueKind, Constraints.tagOrUpper (TagSpace.ofStrings ["ok"] + TagSpace.ofNumbers [123.])) (fun a -> multi [a])

[<Fact(DisplayName = "unify (?es...(?x: 'a'..)) ()")>]
let unifyElementTypeConstrainedMultiVarAndEmpty() =
    let t1 =
        Type.newValueVarWith 1 (C.stringOrUpper "a")
        |> C.multiElementType
        |> Type.newMultiVarWith 1

    unify t1 Type.empty

[<Fact(DisplayName = "unify (?es...(?a := (?x: 'a'..))) ()")>]
let unifyAssignedElementTypeConstrainedMultiVarAndEmpty() =
    let t1 =
        Type.newValueVarWith 1 (C.stringOrUpper "a")
        |> Type.newAssigned
        |> Type.newAssigned
        |> C.multiElementType
        |> Type.newMultiVarWith 1

    unify t1 Type.empty
