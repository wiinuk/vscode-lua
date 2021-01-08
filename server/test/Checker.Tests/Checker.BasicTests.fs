module LuaChecker.Checker.BasicTests
open LuaChecker
open LuaChecker.TypeSystem
open LuaChecker.Checker.Test.Utils
open LuaChecker.Checker.Test.Helpers
open LuaChecker.Checker.Test.TypeExtensions
open LuaChecker.Test
open Xunit
module C = Constraints
module S = Syntaxes
module T = TypedSyntaxes


[<Fact>]
let untilScope() =
    "repeat local x = true until x"
    |> chunkDiagnostics id =? []

[<Fact>]
let undefinedName() =
    "undefinedIdentifier = 10"
    |> chunkDiagnostics id =? [
        Diagnostic({ start = 0; end' = 19 }, Severity.Error, DiagnosticKind.NameNotFound "undefinedIdentifier")
    ]

[<Fact>]
let typeMismatch() =
    """
    local function f() return { x = 1, y = 2 } end
    local a = f()
    local b = a.x + ""
    """
    |> chunkDiagnostics id =? [
        error (90, 92) <| K.UnifyError(ConstraintMismatch(Constraints.stringOrUpper "", Constraints.tagOrLower [types.number]))
    ]

[<Fact>]
let functionType() =
    chunkScheme id "return function() return 1 end" =? type0 ([] ->. [types.number])
    chunkScheme id "return function(a) return a end" =? type1 (fun a -> [a] ->. [a])

[<Fact>]
let idFunction() =
    chunkScheme id "
    local function id(x) return x end
    return id
    " =? type1 (fun a -> [a] ->. [a])

[<Fact>]
let idFunctionInstantiate() =
    chunkResult id "
    local function id(x) return x end
    return id(10), id('a')
    " =? multi [types.number; types.string]

[<Fact>]
let getFieldFunction() =
    chunkScheme id "
    local function f(p) return p.x end
    return f
    " =? forall2 (fun t0 t1 ->
        (Constraints.ofFields ["x", t1], Constraints.any),
        [t0] ->. [t1]
    )

[<Fact>]
let getFieldFunctionInstantiate() =
    chunkResult id "
    local function f(p) return p.x end
    return f { x = 10, y = 20 }, f { x = true }
    " =? multi [types.number; types.boolean]

[<Fact>]
let ifReturn() =
    chunkScheme id "
    if true then return 10 else return 10 end
    " =? types.number

[<Fact>]
let varAndInterfaceRequireField() =
    // unify ('a: { x: number }) { name: string }
    "
    local function f(p) return p.x + 0 end
    return f { name = 'bob' }
    "
    |> chunkDiagnostics id =? [
        RequireField(
            actualFields = Map [FieldKey.String "name", types.string],
            requireKey = FieldKey.String "x",
            requireType = types.number
        )
        |> K.UnifyError
        |> error (57, 73)
    ]

[<Fact>]
let checkVarWithInterface2() =
    // unify ('t: { x: number }) { x: number }
    // unify ('t: { x: number }) { x: number, y: number }
    "
    local function f(p1, p2)
        local _ = p1.x + p2.x
        if true then return p1 else return p2 end
    end
    return f({ x = 10, y = 20 }, { x = 10 })
    "
    |> chunkDiagnostics id =? [
        RequireField(
            actualFields = Map [FieldKey.String "x", types.number],
            requireKey = FieldKey.String "y",
            requireType = types.number
        )
        |> K.UnifyError
        |> error (130, 162)
    ]

[<Fact>]
let simpleGlobalRequire() =
    """
    return require "lib1"
    """
    |> chunkScheme (fun c ->
        { c with
            path = "C:/main.lua"
            sources = [
                {
                    path = "C:/lib1.lua"
                    source = "return 10"
                }
            ]
        }
    )
    =? type0 types.number

[<Fact>]
let nestedTyping() =
    chunkResult id "
    local function pair(x)
        local function f(y) return x, y end
        return f
    end

    local p11, p12 = pair(123)('a')
    local p21, p22 = pair(true)('b')

    return p11, p12, p21, p22
    " =? multi [types.number; types.string; types.boolean; types.string]

[<Fact>]
let recursiveTyping() =
    chunkScheme id "
    local function f(x)
        if true then return 'a'
        else return f(123)
        end
    end
    return f
    " =? type0 ([types.number] ->. [types.string])

[<Fact>]
let multiAssign() =
    chunkScheme id "
    return function(f, g)
        local x, y, z = f(), g()
        return x + y + z
    end
    "
    =?
    // type(m1..., m2...) -> fun(fun() -> (number, m1...), fun() -> (number, number, m2...)) -> number
    type2With (fun c ->
        { c with
            p0 = { c.p0 with kind = types.multiKind }
            p1 = { c.p1 with kind = types.multiKind }
        }) (fun m1 m2 ->
            let number = types.number
            let f = types.fn(types.empty, number^^m1)
            let g = types.fn(types.empty, number^^number^^m2)
            [f; g] ->. [number]
        )

[<Fact>]
let varArgToSingle() =
    chunkScheme id "
    return function(x, ...)
        return x + ...
    end
    " =?
    // fun(number, number, ...) -> number
    type1With (fun c ->
        { c with
            p0 = { c.p0 with kind = types.multiKind }
        })
        (fun m1 -> types.fn(types.number^^types.number^^m1, multi [types.number]))

[<Fact>]
let polyVarParameter() =
    chunkScheme id "
    return function(x, ...) end
    " =?
    type2With (fun c ->
        { c with
            p1 = { c.p1 with kind = types.multiKind }
        })
        (fun p0 p1 ->
            types.fn(p0^^p1, types.empty)
        )

[<Fact>]
let callMulti() =
    chunkScheme id "
    return function(f, g) return f(10, g()) end
    "
    =?
    type2With (fun c ->
        { c with
            p0 = { c.p0 with kind = types.multiKind }
            p1 = { c.p1 with kind = types.multiKind }
        }) (fun p0 p1 ->
        let f = types.fn(types.number^^p0, p1)
        let g = types.fn(types.empty, p0)
        types.fn(multi [f; g], p1)
    )

[<Fact>]
let assignMulti() =
    chunkScheme id "
    return function(...)
        local a = 1, nil, 'a', ...
        return a
    end
    "
    =?
    type1With (fun c -> { c with p0 = { c.p0 with kind = types.multiKind } }) (fun p0 ->
        types.fn(p0, multi [types.number])
    )

[<Fact>]
let multiLocalTooLong() =
    chunkDiagnostics id "
    local a, b = 10
    " =? []

[<Fact>]
let iteratorMultiVar() =
    chunkScheme id "
    return function(f) for x, y, z in f() do local _ = x + y + z end end
    "
    =?
    type1 (fun s ->
        let v = types.number
        let it = [s; v] ->. [v; types.number; types.number]
        let f = [] ->. [it; s; v]
        [f] ->. []
    )

[<Fact>]
let consConstraintAndDiscord() =
    chunkScheme id "
    return function(...)
        local a, b = ...
        return 10 + ...
    end
    "
    =?
    // type(a, b...) -> fun(number, a, b...) -> number
    type2With (fun c -> { c with p1 = { c.p1 with kind = types.multiKind } }) (fun a b ->
        types.fn(types.number^^a^^b, multi [types.number])
    )

[<Fact(DisplayName = "`f()` ( statement )")>]
let emptyResultTypeConstraint() =
    chunkScheme id "
    return function(f) f() end
    "
    =? type0 ([[] ->. []] ->. [])

[<Fact(DisplayName = "`g(f(), x)`")>]
let discordResultTypeRest() =
    chunkScheme id "
    return function(f, g, x) g(f(), x) end
    "
    // type(fr, frs..., x) -> fun(fun() -> (fr, frs...), fun(fr, x) -> (), x) -> ()
    =? type3With (fun c -> { c with p1 = { c.p1 with kind = types.multiKind } }) (fun fr frs x ->
        [types.fn(types.empty, fr^^frs); [fr; x] ->. []; x] ->. []
    )

[<Fact(DisplayName = "`g(x, f())`")>]
let copyMultiValue() =
    chunkScheme id "
    return function(f, g, x) g(x, f()) end
    "
    =?
    scheme2With (
        (types.multiKind, Constraints.any),
        (types.valueKind, Constraints.any)
    ) (fun fr x ->
        let f = types.fn(types.empty, fr)
        let g = types.fn(x^^fr, types.empty)
        [f; g; x] ->. []
    )

[<Fact(DisplayName = "`local a, b, c = f(), x`")>]
let ignoreAssignValue() =
    chunkDiagnostics id "
    return function(f, x) local a, b, c = f(), x; return a + b + c end
    "
    |> function
    | [Diagnostic({ start = 66; end' = 67 }, Severity.Error, DiagnosticKind.UnifyError(ConstraintMismatch _))] -> ()
    | x -> failwithf "%A" x

[<Fact(DisplayName = "`return f()`")>]
let transportResult() =
    chunkScheme id "
    return function(f) return f() end
    "
    =?
    scheme1With (types.multiKind, Constraints.any) (fun fr ->
        types.fn(multi [types.fn(types.empty, fr)], fr)
    )

[<Fact(DisplayName = "`return ...`")>]
let transportVarArg() =
    chunkScheme id "
    return function(...) return ... end
    "
    =?
    scheme1With (types.multiKind, Constraints.any) (fun va ->
        types.fn(va, va)
    )

[<Fact(DisplayName = "`x, y, f()`")>]
let returnRestFunctionResult() =
    chunkScheme id "
    return function(x,y,f) return x,y,f() end
    "
    =?
    scheme3With (
        (types.valueKind, Constraints.any),
        (types.valueKind, Constraints.any),
        (types.multiKind, Constraints.any)
    ) (fun x y fr ->
        let f = types.fn(types.empty, fr)
        types.fn(multi [x; y; f], x^^y^^fr)
    )

[<Fact(DisplayName = "`{f()}`")>]
let newTableLastCall() =
    chunkScheme id "
    return function(f) return {f()} end
    "
    =?
    forall2With (types.multiKind, types.valueKind) (fun p0 p1 ->
        (MultiElementTypeConstraint p1 |> withEmptyLocation, Constraints.any),
        [types.fn(types.empty, p0)] ->. [types.table(types.number, p1)]
    )
[<Fact(DisplayName = "`{...}`")>]
let newTableLastVarArgTyping() =
    chunkScheme id "
    return function(...) return {...} end
    "
    =?
    forall2With (types.multiKind, types.valueKind) (fun p0 p1 ->
        (MultiElementTypeConstraint p1 |> withEmptyLocation, Constraints.any),
        types.fn(p0, multi [types.table(types.number, p1)])
    )

[<Fact(DisplayName = "`{f(), 'a'}`")>]
let newTableNonLastCallTyping() =
    chunkScheme id "
    return function (f) return {f(), 'a'} end
    "
    =?
    // type(m...) -> fun(fun() -> (string, m...)) -> table<number, string>
    type1With (fun c -> { c with p0 = { c.p0 with kind = types.multiKind } }) (fun m ->
        [types.fn(types.empty, types.string^^m)] ->. [types.table(types.number, types.string)]
    )

[<Fact>]
let rank1Type() =
    chunkScheme id "
    local function f(x) return x end
    local x = { f1 = f, f2 = f }
    local f = x.f1
    local x = { f1 = f, f2 = f }
    return x
    "
    =?

    // x: { f1: type '0. fun('0): ('0), f2: type '0. fun('0): ('0) }
    let p0 = TypeParameterId.createNext types.valueKind
    let t0 = ParameterType p0 |> Type.makeWithEmptyLocation
    let t = TypeAbstraction([TypeParameter("", p0, Constraints.any)], [t0] ->. [t0]) |> Type.makeWithEmptyLocation
    Type.interfaceType [
        "f1", t
        "f2", t
    ]
    |> Scheme.normalize

[<Fact>]
let curriedFunctionGeneralize() =
    chunkResult id "
    local function f(x) return function(y) return { x = x, y = y } end end
    local with1 = f(1)
    return with1
    "
    =? multi [
        type1 <| fun y -> [y] ->. [Type.interfaceType ["x", types.number; "y", y]]
    ]

[<Fact>]
let unifyVarAndTypeAbs() =
    // type(y) -> fun(y) -> { x: (?x(2): 1..); y: y; }
    let with1T =
        let x = Type.newValueVarWith 2 <| Constraints.numberOrUpper 1.
        type1 <| fun y -> [y] ->. [Type.interfaceType ["x", x; "y", y]]

    // ?a(2)
    let a = Type.newVar 2

    // unify (type(y) -> fun(y) -> { x: (?x(2): 1..); y: y; }) (?a(2))
    unify with1T a =? ValueNone

    Scheme.normalize a =? type1 (fun y -> [y] ->. [Type.interfaceType ["x", types.number; "y", y]])

[<Fact>]
let curriedFunctionRank1() =
    chunkResult id "
    local function f(x)
        return function(y)
            return { f1 = x, f2 = y }
        end
    end

    local f1 = f(1)

    return f1(true), f1('abc')
    "
    =? multi [
        type0 <| Type.interfaceType [
            "f1", types.number
            "f2", types.boolean
        ]
        type0 <| Type.interfaceType [
            "f1", types.number
            "f2", types.string
        ]
    ]

[<Fact>]
let unifyTypeAbstraction() =
    chunkResult id "
    local function id1(x) return x end
    local function id2(x) return x end
    local id = id1
    id = id2
    "
    =? multi []

[<Fact>]
let recursiveConstraint() =
    chunkScheme id "
        local function getArea(shape) return shape:area() end
        return getArea {
            _width = 10,
            _height = 20,
            area = function(self) return self._width * self._height end
        }
    "
    =? types.number

[<Fact>]
let recursiveConstraintMissingFieldError() =
    chunkDiagnostics id "
        local function getArea(shape) return shape:area() end
        return getArea {
            area = function(self) return self._missingField + 0 end
        }
    "
    =? [
        RequireField(
            Map [
                FieldKey.String "area", scheme1With (types.valueKind, Constraints.ofFields ["_missingField", types.number]) <| fun t1 ->
                    [t1] ->. [types.number]
            ],
            FieldKey.String "_missingField",
            types.number
        )
        |> K.UnifyError
        |> error (86, 165)
    ]

[<Fact>]
let recursiveConstraint2() =
    chunkScheme id "
    local function getInfo(shape) return { area1 = shape:area(); area2 = shape:scale(2):scale(3):area() } end
    return getInfo {
        _w = 4,
        _h = 5,
        area = function(self) return self._w * self._h end,
        scale = function(self, x) return { _w = self._w * x; _h = self._h * x; area = self.area; scale = self.scale } end,
    }
    "
    =? Type.interfaceType [
        "area1", types.number
        "area2", types.number
    ]

[<Fact>]
let recursiveConstraint2MissingFieldError() =
    chunkDiagnostics id "
    local function getInfo(shape) return { area1 = shape:area(); area2 = shape:scale(2):scale(3):area() } end
    return getInfo {
        width = 4,
        _h = 5,
        area = function(self) return self._w * self._h end,
        scale = function(self, x) self._w = self._w * x; self._h = self._h * x; return self end,
    }
    "
    =? List.map Diagnostic.normalize [
        RequireField(
            Map [
                FieldKey.String "_h", scheme1With (types.valueKind, Constraints.ofSpace([Type.numberLiteralType 5.], [types.number])) <| fun t1 -> t1
                FieldKey.String "area", scheme1With
                    (types.valueKind, Constraints.ofFields ["_h", types.number; "_w", types.number]) (fun t1 ->
                        [t1] ->. [types.number]
                    )

                FieldKey.String "scale", forall1 <| fun t1 ->
                    Constraints.ofFields ["_h", types.number; "_w", types.number], [t1; types.number] ->. [t1]

                FieldKey.String "width", types.number
            ],
            FieldKey.String "_w",
            types.number
        )
        |> K.UnifyError
        |> error (130, 329)
    ]

[<Fact>]
let acceptRecursiveType1() =
    chunkDiagnostics id "
    local function f(n) return (f) end
    return f(42)
    " =? []

[<Fact>]
let acceptRecursiveType2() =
    chunkDiagnostics id "
    local function f(x) return x(x) end
    " =? []

[<Fact>]
let acceptRecursiveType3() =
    chunkDiagnostics id "
    local function x() return { [1] = 1, [2] = x() } end
    return x()
    " =? []

[<Fact>]
let acceptRecursiveType4() =
    chunkDiagnostics id "
    local function f(n)
        return function()
            return { item1 = n, item2 = f(n + 1) }
        end
    end
    return f(0)
    "
    =? []

[<Fact>]
let ifAndReturnTagSpaceConstraint() =
    chunkScheme id "
    local function f(x)
        if x
        then return 'ok'
        else return 123
        end
    end
    return f(true)
    "
    =?

    // type(a: (123 | "ok")..) -> a
    scheme1With (types.valueKind, Constraints.literalsOrUpper [S.String "ok"; S.Number 123.]) id

[<Fact(DisplayName = "'ok' or 123")>]
let orOperatorTyping() =
    chunkScheme id "return 'ok' or 123"
    =?
    // type(a: ("ok" | 123)..) -> a
    scheme1With (types.valueKind, Constraints.literalsOrUpper [S.String "ok"; S.Number 123.]) id

[<Fact>]
let localGeneralize() =
    chunkResult id "
    local x = 'ok' or 123
    return x, x
    "
    =?
    let c = Constraints.literalsOrUpper [S.String "ok"; S.Number 123.]
    let t = type1With (fun o -> { o with t = { o.t with normalize = id }; p0 = { o.p0 with c = fun _ -> c } }) id
    multi [t; t]
    |> Scheme.normalize

[<Fact>]
let localGeneralizeAndUnion() =
    chunkResult id "
    local x1 = 'ok' or 123
    local x2 = x1 or true
    local x3 = x1 or nil
    return x2, x3
    "
    =?
    let s = [S.String "ok"; S.Number 123.]
    let c1 = Constraints.literalsOrUpper [yield! s; S.True]
    let c2 = Constraints.literalsOrUpper [yield! s; S.Nil]
    let t1 = type1With (fun c -> { c with t = { c.t with normalize = id }; p0 = { c.p0 with c = fun _ -> c1 } }) id
    let t2 = type1With (fun c -> { c with t = { c.t with normalize = id }; p0 = { c.p0 with c = fun _ -> c2 } }) id
    multi [
        t1
        t2
    ]
    |> Scheme.normalize

[<Fact>]
let typeLocation() =
    checkChunk id "
    local x = 'a'
    local y = 1
    return x + y
    "
    |> snd
    =? [
        let c =
            Constraints.tagOrUpper [
                LiteralType(S.String "a")
                |> Type.makeWithLocation [location "C:/dir/file.lua" (15, 18)]
            ]
            |> Constraints.withLocation [location "C:/dir/file.lua" (15, 18)]

        let t =
            Constraints.tagOrLower [
                types.number
            ]
            |> Constraints.withLocation [location "C:/dir/file.lua" (48, 49)]

        ConstraintMismatch(c, t)
        |> K.UnifyError
        |> error (46, 47)
    ]

[<Fact>]
let implicitReturnWithDoStat() =
    chunkScheme id "
    local function f(x)
        do return 123 end
    end
    return f(true)
    "
    =? types.number

[<Fact>]
let implicitReturnWithWhileStat() =
    chunkScheme id "
    local function f(x)
        while x do return 123 end
    end
    return f(true)
    "
    =? type1WithConstraints (C.literalsOrUpper [S.Nil; S.Number 123.]) id

[<Fact>]
let implicitReturnWithDoUntilStat() =
    chunkScheme id "
    local function f(x)
        repeat return 123 until x
    end
    return f(true)
    "
    // type(x: (nil | 123)..) -> x
    =? type1WithConstraints (C.literalsOrUpper [S.Nil; S.Number 123.]) id

[<Fact>]
let implicitReturnWithIfStat() =
    let success source =
        chunkResult id source =? multi [types.number]

    let successNilOrNumber source =
        chunkScheme id source
        =? type1WithConstraints (C.literalsOrUpper [S.Nil; S.Number 123.]) id

    successNilOrNumber "
    local function f(x)
        if x then return 123 end
    end
    return f(true)
    "

    successNilOrNumber "
    local function f(x)
        if x then return 123 else end
    end
    return f(true)
    "

    successNilOrNumber "
    local function f(x)
        if x then else return 123 end
    end
    return f(true)
    "

    success "
    local function f(x)
        if x then return 123 else return 123 end
    end
    return f(true)
    "

    successNilOrNumber "
    local function f(x)
        if x then return 123 elseif x then end
    end
    return f(true)
    "

    successNilOrNumber "
    local function f(x)
        if x then elseif x then return 123 end
    end
    return f(true)
    "

    successNilOrNumber "
    local function f(x)
        if x then return 123 elseif x then return 123 end
    end
    return f(true)
    "

    successNilOrNumber "
    local function f(x)
        if x then return 123 elseif x then else end
    end
    return f(true)
    "

    successNilOrNumber "
    local function f(x)
        if x then elseif x then return 123 else end
    end
    return f(true)
    "

    successNilOrNumber "
    local function f(x)
        if x then elseif x then else return 123 end
    end
    return f(true)
    "

    successNilOrNumber "
    local function f(x)
        if x then return 123 elseif x then return 123 else end
    end
    return f(true)
    "

    successNilOrNumber "
    local function f(x)
        if x then return 123 elseif x then else return 123 end
    end
    return f(true)
    "

    successNilOrNumber "
    local function f(x)
        if x then elseif x then return 123 else return 123 end
    end
    return f(true)
    "

    success "
    local function f(x)
        if x then return 123 elseif x then return 123 else return 123 end
    end
    return f(true)
    "

[<Fact>]
let implicitReturnWithFor() =
    chunkScheme id "
    local function f(x)
        for _ = 0, 10 do return 123 end
    end
    return f(true)
    "
    =? type1WithConstraints (C.literalsOrUpper [S.Nil; S.Number 123.]) id

[<Fact>]
let multiValueRestAsNilOrUpper() =
    chunkScheme id "
    local function f() end
    local x = f()
    return x
    "
    =? types.nil

[<Fact>]
let multiValueRestAsNilOrUpperGeneric() =
    chunkResult id "
    local function f() end
    local x1 = f()
    return x1 or 10, x1 or 'a'
    "
    =? type2WithConstraints (C.literalsOrUpper [S.Nil; S.Number 10.], C.literalsOrUpper [S.Nil; S.String "a"]) (fun a b ->
        multi [a; b]
    )

[<Fact>]
let emptyReturnAsNilOrUppers() =
    chunkResult id "
    local function f() return end
    local x, y = f()
    return x, y, 10
    "
    =? multi [types.nil; types.nil; types.number]

[<Fact>]
let returnRestAsNilOrUppers() =
    chunkResult id "
    local function f() return 10 end
    local x, y = f()
    return x, y, 10
    "
    =? multi [types.number; types.nil; types.number]

[<Fact>]
let multiTypeAsSingleType() =
    chunkScheme id "
    local function f(g)
        local x = (g())
        local y, z = g()
        return x + y + z
    end
    return f
    "
    =?
    // fun(fun() -> (number, number, ...)) -> number
    type1With (fun c -> { c with p0 = { c.p0 with kind = types.multiKind } }) (fun m1 ->
        let number = types.number
        let g = types.fn(types.empty, number^^number^^m1)
        [g] ->. [number]
    )

[<Fact>]
let resultRest() =
    chunkResult id "
    local function f(g) local x, y = g(); return x + y end
    local x1 = f(function() return 1, 2 end)
    local x2 = f(function() return 1, 2, true end)
    local x3 = f(function() return 1, 2, 'a' end)
    local x4 = f(function() return 1, 2, nil end)
    return x1, x2, x3, x4
    "
    =? multi [types.number; types.number; types.number; types.number]

[<Fact>]
let resultRestError1() =
    chunkDiagnostics id "
    local function f(g) local x, y = g(); return x + y end
    return f(function() return 1 end)
    "
    =? [
        ConstraintMismatch(C.literalsOrUpper [S.Nil], C.tagOrLower [types.number])
        |> K.UnifyError
        |> error (72, 97)
    ]

[<Fact>]
let resultRestError2() =
    chunkDiagnostics id "
    local function f(g) local x, y = g(); return x + y end
    return f(function() return 1, 'a' end)
    "
    =? [
        ConstraintMismatch(C.stringOrUpper "a", C.tagOrLower [types.number])
        |> K.UnifyError
        |> error (72, 102)
    ]

[<Fact>]
let localMultiTyping() =
    chunkResult id "
    local function f() return 1, 2 end

    local x = f()
    local x, y = f()
    local x, y, z = f()
    local zn = z or 10
    return z, zn
    "
    // nil, (type(zn: (nil | 10)..) -> zn)
    =? multi [
        types.nil
        type1WithConstraints (C.literalsOrUpper [S.Nil; S.Number 10.]) id
    ]

[<Fact>]
let returnTypeOfDifferentLength() =
    chunkResult id "
    ---@global x boolean
    if x then return true end
    "
    =? type1WithConstraints (C.literalsOrUpper [S.True; S.Nil]) (fun r ->
        multi [r]
    )

[<Fact>]
let returnTypeOfDifferentLengthBinaryOp() =
    chunkResult id "
    ---@global x boolean
    if x then return 1 / 2 end
    "
    =? type1WithConstraints (C.tagOrUpper [Type.literalType S.Nil; types.number]) (fun r ->
        multi [r]
    )

[<Fact>]
let standardLibraryIsAutomaticallyLoaded() =
    projectSchemes id [
        "return math.max(3, 4)" &> "main"

        Check "main"
    ] =? [
        Ok types.number
    ]

[<Fact>]
let stringField() =
    chunkResult id "
    ---@global x string
    return x.upper(x)
    "
    =? multi [
        types.string
    ]

[<Fact>]
let stringLiteralMethod() =
    chunkResult id "
    return ('abc'):byte(1)
    "
    =? multi [
        types.number
    ]

[<Fact>]
let stringLiteralField() =
    chunkResult id "
    return ('abc').char(1, 2, 3)
    "
    =? multi [
        types.string
    ]

[<Fact>]
let stringLiteralMetaTable() =
    chunkResult (fun c -> { c with projectConfig = { c.projectConfig with initialGlobalModulePaths = [] } }) "
    ---@_Feature stringMetaTableIndex
    ---@class MyStringMetaTable
    ---@field myField number

    return ('X').myField
    "
    =? multi [
        types.number
    ]

[<Fact>]
let stringLiteralAsInterface() =
    chunkResult id "
    local function getUpperField(x) return x.upper end
    return getUpperField('a')('')
    "
    =? multi [
        types.string
    ]

[<Fact>]
let implicitSelfTyping() =
    chunkResult id "
    local p = {
        x = 1 + 2,
        m = function(self) return 1 + 2 end
    }
    function p:m() return self.x end
    return p:m()
    "
    =? multi [
        types.number
    ]

[<Fact>]
let implicitSelfParameters() =
    chunkResult id "
    local p = {
        x = 1 + 2,
        m = function(self, v1, v2) return v1 + v2 end
    }
    function p:m(v1, v2) return self.x + v1 + v2 end
    return p:m(1, 2)
    "
    =? multi [
        types.number
    ]

[<Fact>]
let implicitSelfParametersWithVariadic() =
    chunkResult id "
    local p = {
        x = 1 + 2,
        m = function(self, v1, v2, ...) return v1 + v2 end
    }
    function p:m(v1, v2, ...) return self.x + v1 + v2 end
    return p:m(1, 2)
    "
    =? multi [
        types.number
    ]

[<Fact>]
let implicitSelfVariadic() =
    chunkResult id "
    local p = {
        x = 1 + 2,
        getX = function(self, ...) return 1 + 2 end
    }
    function p:getX(...) return self.x end
    return p:getX()
    "
    =? multi [
        types.number
    ]

[<Fact>]
let implicitSelfAndExplicitSelf() =
    chunkResult id "
    local p = {
        x = 1 + 2,
        m = function(self, self) return 'a' .. 'b' end
    }
    function p:m(self) return self end
    return p:m 'X'
    "
    =? multi [
        types.string
    ]

[<Fact>]
let loopAndReturn() =
    chunkResult id "
    local function f()
        while true do
            return 123 + 456
        end
    end
    return f()
    "
    =? multi [
        types.number
    ]

[<Fact>]
let loopAndIfReturn() =
    chunkResult id "
    local function f(b)
        while true do
            if b then return 123 + 456 end
        end
    end
    return f(false)
    "
    =? multi [
        types.number
    ]

[<Fact>]
let loopAndBreak() =
    chunkResult id "
    local function f()
        while true do break end
    end
    return f()
    "
    =? multi []

[<Fact>]
let loopAndBreakAfterReturn() =
    chunkResult id "
    local function f()
        while true do break end
        return 123
    end
    return f()
    "
    =? multi [
        types.number
    ]

[<Fact>]
let loopAndInnerBreakAndReturn() =
    chunkResult id "
    local function f()
        while true do
            while true do break end
            return 123
        end
    end
    return f()
    "
    =? multi [
        types.number
    ]

[<Fact>]
let add10() =
    chunkResult id "
    return 10 + 10
    "
    =? multi [
        types.number
    ]

[<Fact>]
let tableLength() =
    chunkResult id "
    return #{1}
    "
    =? multi [types.number]
