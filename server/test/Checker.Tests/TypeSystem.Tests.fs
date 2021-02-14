module LuaChecker.TypeSystem.Tests
open Xunit
open LuaChecker
open LuaChecker.Checker.Test.Utils
open LuaChecker.Checker.Test.TypeExtensions
open LuaChecker.Checker.Test.Helpers
open LuaChecker.Parser.Tests
open LuaChecker.Syntax
open LuaChecker.Test
module T = TypedSyntaxes
module C = Constraints
module S = Syntaxes


[<Fact>]
let unifyVarAndNumber() =
    let t1 = Type.newVar 1
    unify t1 types.number =? ValueNone
    Scheme.normalize subst' t1 =? type0 types.number

[<Fact>]
let unifyVarAndVar() =
    // unify 'a 'b = ['a = 'b]
    let a = Type.newVar 1
    let b = Type.newVar 1
    unify a b =? ValueNone
    ([a; b] ->. []) |> Scheme.normalize subst' =? type1 (fun a -> [a; a] ->. [])

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
    |> Scheme.normalize subst'
    =? forall2 (fun t0 t1 ->
        (Constraints.ofFields ["x", types.number; "y", types.string; "z", t1], Constraints.any),
        [t0; t0; types.string; types.number; t1] ->. []
    )

[<Fact>]
let multi2VarSchemeRoundTrip() =
    // type 'a. fun('a, 'a): ()
    let t = type1 (fun a -> [a; a] ->. [])
    let struct(_, t) = t |> Scheme.instantiate subst' 1 in t |> Scheme.normalize subst' =? type1 (fun a -> [a; a] ->. [])

[<Fact>]
let unifyVarAndInterface() =
    // unify (?a: { x: number }) { x: ?x } => [?a = { x: ?x }; ?x = number]
    let t1 = Type.newVarWithFields 1 ["x", types.number]
    let t2 = Type.interfaceType ["x", Type.newVar 1]
    unify t1 t2 =? ValueNone
    [t1; t2] ->. [] |> Scheme.normalize subst'
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
let typedHitTest() =
    let normalize subst _ t = Type.apply { visitedVars = []; other = { varToTypeParameter = []; subst = subst } } t |> Scheme.normalize subst
    let getNormalizedType subst t _ _ = normalize subst () t

    let push this x =
        let subst, xs = !this
        this := subst, x::xs

    let subst this = fst !this
    let visitor state = { new TypedSyntaxVisitorBase() with
        override _.Visit() = failwith ""

        override _.Var(T.Var(name = Name n; varType = t; leaf = l), e) =
            push state (TokenKind.Name n.kind, n.trivia.span, getNormalizedType (subst state) t l e)
        override _.Reserved(T.ReservedVar(s, k, t, l), e) = push state (k, s.span, getNormalizedType (subst state) t l e)
        override _.Literal(x, t, _, _) =
            let subst = subst state
            push state (TokenKind.ofLiteralKind x.kind, x.trivia.span, normalize subst 0 <| Scheme.normalize subst t)
    }

    let test i source =
        match checkChunk id source with
        | Some s, [] ->
            let result = ref (s.typeSubstitute, [])
            let mutable visitor = polyVisitor <| visitor result
            if LuaChecker.Block.hitTest &visitor i s.semanticTree then
                match snd !result with
                | [] -> failwith $"empty result: '{source}' @{i} -> []"
                | [x] -> ValueSome x
                | xs -> failwith $"multiple result: %A{xs}"
            else
                match snd !result with
                | [] -> ValueNone
                | xs -> failwith $"has result: %A{xs}"

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

let tokens source (start, end') =
    let push this x = this := x::!this
    let tuple x = x.start, x.end'
    let visitor state = { new TypedSyntaxVisitorBase() with
        override _.Visit() = failwith ""

        override _.Var(T.Var(name = Name n), _) = push state (TokenKind.Name n.kind, tuple n.trivia.span)
        override _.Reserved(T.ReservedVar(trivia = s; kind = k), _) = push state (k, tuple s.span)
        override _.Literal(x, _, _, _) = push state (TokenKind.ofLiteralKind x.kind, tuple x.trivia.span)
    }

    let range = { start = start; end' = end' }
    let result = ref []
    let tree = checkChunk id source |> fst |> Option.get
    let mutable visitor = polyVisitor <| visitor result
    if Block.iterateRange &visitor range tree.semanticTree then
        match !result with
        | [] -> failwith $"empty result: `{source}` @%A{range} -> []"
        | xs -> List.rev xs
    else
        match !result with
        | [] -> []
        | xs -> failwith $"has result: `{source}` @%A{range} -> %A{xs}"

[<Fact>]
let iterateRange() =
    let source = "local function add10(a) return a + 10 end"
    // "" "" "local function add10(a) return a + 10 end"
    tokens source (0, 0) =? []
    // "" "l" "ocal function add10(a) return a + 10 end"
    tokens source (0, 1) =? []
    // "" "local f" "unction add10(a) return a + 10 end"
    tokens source (0, 7) =? []
    // "" "local function " "add10(a) return a + 10 end"
    tokens source (0, 15) =? []
    // "" "local function a" "dd10(a) return a + 10 end"
    tokens source (0, 16) =? [
        TokenKind.Name "add10", (15, 20)
    ]
    // "" "local function add10" "(a) return a + 10 end"
    tokens source (0, 20) =? [
        TokenKind.Name "add10", (15, 20)
    ]
    // "" "local function add10(" "a) return a + 10 end"
    tokens source (0, 21) =? [
        TokenKind.Name "add10", (15, 20)
    ]
    // "" "local function add10(a" ") return a + 10 end"
    tokens source (0, 22) =? [
        TokenKind.Name "add10", (15, 20)
        TokenKind.Name "a", (21, 22)
    ]
    // "" "local function add10(a) return a" " + 10 end"
    tokens source (0, 32) =? [
        TokenKind.Name "add10", (15, 20)
        TokenKind.Name "a", (21, 22)
        TokenKind.Name "a", (31, 32)
    ]
    // "" "local function add10(a) return a + 10" " end"
    tokens source (0, 36) =? [
        TokenKind.Name "add10", (15, 20)
        TokenKind.Name "a", (21, 22)
        TokenKind.Name "a", (31, 32)
        TokenKind.Add, (33, 34)
        TokenKind.Number 10., (35, 37)
    ]
    // "" "local function add10(a) return a + 10 end" ""
    tokens source (0, 41) =? [
        TokenKind.Name "add10", (15, 20)
        TokenKind.Name "a", (21, 22)
        TokenKind.Name "a", (31, 32)
        TokenKind.Add, (33, 34)
        TokenKind.Number 10., (35, 37)
    ]

    // "local function add10(a) return " "a" " + 10 end"
    tokens source (31, 32) =? [
        TokenKind.Name "a", (31, 32)
    ]
    // "local function add10(a) return " "a +" " 10 end"
    tokens source (31, 34) =? [
        TokenKind.Name "a", (31, 32)
        TokenKind.Add, (33, 34)
    ]
    // "local function add10(a) return " "a + 1" "0 end"
    tokens source (31, 36) =? [
        TokenKind.Name "a", (31, 32)
        TokenKind.Add, (33, 34)
        TokenKind.Number 10., (35, 37)
    ]

[<Fact>]
let iterateRangeProperty() = check <| fun block (n1, n2) ->
    let source =
        block
        |> Printer.block {
            config = Printer.PrintConfig.defaultConfig
            printToken = Printer.printToken
        }
        |> String.concat ""

    let start, end' =
        if source.Length = 0 then 0, 0 else

        let n1, n2 = abs n1 % source.Length, abs n2 % source.Length
        min n1 n2, max n1 n2 + 1

    tokens source (0, 0) =? []
    tokens source (start, end') |> ignore

[<Fact(DisplayName = "generalize (?a: { f: ?b }) = (type ('0: { f: '1 }) '1. '0)")>]
let generalizeInterfaceConstraints() =
    let b = Type.newVar 1
    let a = Type.newVarWithFields 1 ["f", b]

    Scheme.generalize subst' 0 a
    |> Scheme.normalize subst'
    =? forall2 (fun t0 t1 -> (Constraints.ofFields ["f", t1], Constraints.any), t0)

[<Fact(DisplayName = "generalize (fun(?m...?a): ()) = (type 'm...'a 'a. fun('m...): ())")>]
let generalizeMultiTypeVarConstraint() =
    let a = Type.newVar 1
    let t = types.fn(MultiType.newVarWith 1 (ValueSome(MultiElementTypeConstraint a |> withEmptyLocation)), types.empty)
    Scheme.generalize subst' 0 t
    |> Scheme.normalize subst'
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
    Scheme.normalize subst' t =? type1 (fun t0 -> [t0] ->. [b])

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
    | { kind = VarType(Subst.Find subst' (Ok { kind = VarType (Subst.Find subst' (Ok { kind = VarType(Var(level = 0)) })) })) } -> ()
    | b -> failwithf "%A" b

[<Fact(DisplayName = "instantiate `type(a) -> type(b) -> fun(a, b) -> ()` = `fun(?x, ?y) -> ()`")>]
let instantiateScheme2() =
    let type1 = type1With <| fun c -> { c with t = { c.t with normalize = id } }

    /// type a. type b. fun(a, b): ()
    let t0 = type1 <| fun t0 -> type1 <| fun t1 -> [t0; t1] ->. []

    /// type a b. fun(a, b): ()
    let t1 = type2 <| fun t1 t2 -> [t1; t2] ->. []

    let struct(_, t) = Scheme.instantiate subst' 1 t0
    Scheme.normalize subst' t =? t1

[<Fact(DisplayName = "instantiate `{ f: type a. fun(a): () }` = `{ f: type a. fun(a): () }`")>]
let instantiateSchemeField() =
    /// { f: type a. fun(a): () }
    let t0 = Type.interfaceType [
        "f", type1 <| fun t0 -> [t0] ->. []
    ]
    let struct(_, t) = Scheme.instantiate subst' 1 t0
    Scheme.normalize subst' t
    =?
    Scheme.normalize subst' t0

[<Fact>]
let unifyRecursiveFunctionType() =
    /// ?f := fun(number): ?f
    let f() =
        let f = Type.newVar 1
        match f.kind with
        | VarType r -> Subst.assign subst' r ([types.number] ->. [f])
        | _ -> ()
        f

    /// ?x := fun(number): (fun(number): ?x)
    let x() =
        let x = Type.newVar 1
        match x.kind with
        | VarType r -> Subst.assign subst' r ([types.number] ->. [[types.number] ->. [x]])
        | _ -> ()
        x

    /// ?y := fun(number): (fun(string): ?y)
    let y() =
        let y = Type.newVar 1
        match y.kind with
        | VarType r -> Subst.assign subst' r ([types.number] ->. [[types.string] ->. [y]])
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
    let struct(_, t1) = Scheme.instantiate subst' 0 gt
    let struct(_, t2) = Scheme.instantiate subst' 0 gt

    // unify (?x: { f: fun(number): ?x }) (?y: { f: fun(number): ?y })
    unify t1 t2 =? ValueNone

[<Fact>]
let typesIsSubset() =
    let ofNumbers = List.map Type.numberLiteralType
    let isSubset t1 t2 = TypeSet.isSubset types' (TypeSet t1) (TypeSet t2)
    let allNumber = [types.number]

    isSubset (ofNumbers []) allNumber =? true
    isSubset (ofNumbers []) (ofNumbers []) =? true
    isSubset (ofNumbers []) (ofNumbers [1.]) =? true
    isSubset (ofNumbers [1.]) (ofNumbers []) =? false
    isSubset (ofNumbers [1.;2.]) (ofNumbers [1.;2.]) =? true
    isSubset (ofNumbers [1.]) (ofNumbers [1.;2.]) =? true
    isSubset (ofNumbers [1.;2.]) (ofNumbers [1.]) =? false
    isSubset (ofNumbers [1.;2.]) (ofNumbers [1.;3.]) =? false
    isSubset allNumber (ofNumbers []) =? false
    isSubset (ofNumbers [1.;2.]) allNumber =? true
    isSubset allNumber (ofNumbers [1.;2.]) =? false
    isSubset allNumber allNumber =? true

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
let unifyStringSpaceConstraintInMulti() =
    let r = MultiType.newVar 1
    let r1 = multi [stringT "ok"]
    let r2 = multi [numberT 123.]
    unify r r1 =? ValueNone
    unify r r2 =? ValueNone

    Scheme.normalize subst' r
    =?
    // type(a: ("ok" | 123)..) -> (a,)
    scheme1With (types.valueKind, Constraints.literalsOrUpper [S.String "ok"; S.Number 123.]) (fun a -> multi [a])

[<Fact(DisplayName = "unify (?es...(?x: 'a'..)) ()")>]
let unifyElementTypeConstrainedMultiVarAndEmpty() =
    let t1 =
        Type.newValueVarWith 1 (C.stringOrUpper "a")
        |> C.multiElementType
        |> Type.newMultiVarWith 1

    unify t1 Type.empty =? ValueNone

[<Fact(DisplayName = "unify (?es...(?a := (?x: 'a'..))) ()")>]
let unifyAssignedElementTypeConstrainedMultiVarAndEmpty() =
    let t1 =
        Type.newValueVarWith 1 (C.stringOrUpper "a")
        |> Type.newAssigned subst'
        |> Type.newAssigned subst'
        |> C.multiElementType
        |> Type.newMultiVarWith 1

    unify t1 Type.empty =? ValueNone

[<Fact(DisplayName = "unify string (?x: { upper: fun(string) -> string })")>]
let stringAsInterface() =
    let upperType = types.fn(types.string, types.string)
    let typeEnv =
        { typeEnv' with
            stringTableTypes = [
                Type.interfaceType [
                    "upper", upperType
                ]
            ]
        }

    let t1 = types.string
    let t2 = Type.newVarWithFields 1 ["upper", upperType]
    Type.unify typeEnv t1 t2 =? ValueNone

[<Fact>]
let unifyNumberLiteralAndNumberConstraint() =
    /// 10..
    let t1 = Type.newValueVarWith 1 (Constraints.numberOrUpper 10.)
    /// ..number
    let t2 = Type.newValueVarWith 1 (Constraints.tagOrLower [types.number])
    unify t1 t2 =? ValueNone

[<Fact>]
let unifyTableAndTableConstraint() =

    /// `table<number, number>`
    let t1 = types.table(types.number, types.number)

    /// `?a: ..table<number, ?v>`
    let t2 =
        let v = Type.newValueVarWith 1 Constraints.any
        Type.newValueVarWith 1 (Constraints.tagOrLower [types.table(types.number, v)])

    unify t1 t2 =? ValueNone

[<Fact>]
let unifyRecursiveSelfConstraintAndTypeAbstraction() =
    let self = Var.newVar "self" 1 types.valueKind Constraints.any

    let x =
        Constraints.ofFields ["field", VarType self |> Type.makeWithEmptyLocation]
        |> Type.newValueVarWith 1

    // t1 = `?x: { field: ?self }`
    let t1 = x

    // t2 = `{ field: type(a) -> a }`
    let t2 = Type.interfaceType [
        "field", forall1 <| fun a -> Constraints.any, a
    ]

    // subst = [ ?self |-> ?x ]
    let subst = Subst.create()
    Subst.assign subst self x

    Type.unify { system = types'; substitute = subst; stringTableTypes = [] } t1 t2 =? ValueNone

[<Fact>]
let unifyRecursiveType1() =

    // t1 = `?self`
    let self' = Var.newVar "self" 1 types.valueKind Constraints.any
    let self = VarType self' |> Type.makeWithEmptyLocation

    // t2 = `{ f: type(a) -> fun(a) -> a }`
    let t2 = Type.interfaceType [
        "f", forall1 <| fun a -> Constraints.any, [a] ->. [a]
    ]

    // subst = [?self |-> ?x1: { f: fun(?self) -> ?x2 }]
    let subst = Subst.createOfSeq [
        self', Type.newValueVarWith 1 <| Constraints.ofFields [ "f", [self] ->. [Type.newValueVarWith 1 Constraints.any] ]
    ]

    Type.unify { system = types'; substitute = subst; stringTableTypes = [] } self t2 =? ValueNone

[<Fact>]
let unifyRecursiveType() =

    // t1 = `?self`
    let self' = Var.newVar "self" 1 types.valueKind Constraints.any
    let self = VarType self' |> Type.makeWithEmptyLocation

    // t2 = `{ getGreeter: type(a) -> fun(a) -> a; greet: type(a) -> fun(a) -> () }`
    let t2 = Type.interfaceType [
        "getGreeter", forall1 <| fun a -> Constraints.any, [a] ->. [a]
        "greet", forall1 <| fun a -> Constraints.any, [a] ->. []
    ]

    let greeter' = Var.newVar "greeter" 1 types.valueKind Constraints.any
    let greeter = VarType greeter' |> Type.makeWithEmptyLocation

    // subst = [
    //     ?self |-> ?self2 extends { getGreeter: fun(?self) -> ?greeter }`
    //     ?greeter |-> ?greeter2 extends { greet: fun(?greeter) -> () }
    // ]
    let subst = Subst.createOfSeq [
        self', Type.newValueVarWith 1 <| Constraints.ofFields [ "getGreeter", [self] ->. [greeter] ]
        greeter', Type.newValueVarWith 1 <| Constraints.ofFields [ "greet", [greeter] ->. [] ]
    ]

    Type.unify { system = types'; substitute = subst; stringTableTypes = [] } self t2 =? ValueNone
