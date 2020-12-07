module LuaChecker.Checker.Annotations.Tests
open Xunit
open LuaChecker
open LuaChecker.Checker.Test.Utils
open LuaChecker.Checker.Test.Helpers
open LuaChecker.Checker.Test.TypeExtensions
open LuaChecker.Primitives
open LuaChecker.TypeSystem
type private K = LuaChecker.DiagnosticKind


[<Fact(DisplayName = "`--[[---@type string]](10)`")>]
let simpleReinterpretCast() =
    chunkScheme id "return --[[---@type string]](10)"
    =? type0 types.string

[<Fact(DisplayName = "`--[[---@type a]](10)`")>]
let asTypeVar() =
    chunkScheme id "return --[[---@type a]](10)"
    =? type1 (fun a -> a)

[<Fact>]
let specialTypeVarName() =
    chunkScheme id "return --[[---@type any]](10)"
    =? type1 (fun a -> a)

    chunkScheme id "return --[[---@type _]](10)"
    =? type1 (fun a -> a)

[<Fact>]
let validTypeVarName() =
    chunkScheme id "return --[[---@type x]](10)"
    =? type1 (fun a -> a)

    chunkScheme id "return --[[---@type U]](10)"
    =? type1 (fun a -> a)

    chunkScheme id "return --[[---@type T]](10)"
    =? type1 (fun a -> a)

    chunkScheme id "return --[[---@type TType]](10)"
    =? type1 (fun a -> a)

    chunkScheme id "return --[[---@type T2]](10)"
    =? type1 (fun a -> a)

    chunkScheme id "return --[[---@type TAXI]](10)"
    =? type1 (fun a -> a)

    chunkScheme id "return --[[---@type T_]](10)"
    =? type1 (fun a -> a)

[<Fact(DisplayName = "`--[[---@type UndefinedTypeName]](10)`")>]
let invalidTypeVarNameUpper() =
    chunkDiagnostics id "return --[[---@type UndefinedTypeName]](10)"
    =? [
        error (20, 37) <| K.TypeNameNotFound "UndefinedTypeName"
    ]

[<Fact(DisplayName = "`--[[---@type undefinedTypeName]](10)`")>]
let invalidTypeVarNameLower() =
    chunkDiagnostics id "return --[[---@type undefinedTypeName]](10)"
    =? [
        error (20, 37) <| K.TypeNameNotFound "undefinedTypeName"
    ]

[<Fact(DisplayName = "`--[[---@type TypeNameUndefined]](10)`")>]
let invalidTypeVarNameStartsWithT() =
    chunkDiagnostics id "return --[[---@type TypeNameUndefined]](10)"
    =? [
        error (20, 37) <| K.TypeNameNotFound "TypeNameUndefined"
    ]

[<Fact(DisplayName = "`--[[---@type table<T, T>]](10)`")>]
let varTypeEq() =
    chunkScheme id "return --[[---@type table<T, T>]](10)"
    =? type1 (fun a -> types.table(a, a))

[<Fact(DisplayName = "`--[[---@type table<any, any>]](10)`")>]
let specialVarTypeAny() =
    chunkScheme id "return --[[---@type table<any,any>]](10)"
    =? type2 (fun a b -> types.table(a, b))

[<Fact(DisplayName = "`--[[---@type table<_, _>]](10)`")>]
let specialVarTypeHole() =
    chunkScheme id "return --[[---@type table<_, _>]](10)"
    =? type2 (fun a b -> types.table(a, b))

[<Fact(DisplayName = "`--[[---@type string<number>]](10)`")>]
let typeArity() =
    chunkDiagnostics id "return --[[---@type string<number>]](10)"
    =? [
        error (20, 26) <| K.TypeArityMismatch(expectedArity = 0, actualArity = 1)
    ]

[<Fact(DisplayName = "`--[[---@type string[][] ]](10)`")>]
let arrayType() =
    chunkScheme id "return --[[---@type string[][] ]](10)"
    =? type0 (arrayT(arrayT types.string))

[<Fact>]
let duplicateInterfaceTypeField() =
    chunkDiagnostics id "return --[[---@type { x: a, x: b } ]](10)"
    =? [
        info (28, 29) <| K.DuplicateFieldKey(FieldKey.String "x", { start = 22; end' = 23 })
    ]

[<Fact>]
let duplicateInterfaceTypeField2() =
    chunkDiagnostics id "return --[[---@type { x: number, x: number } ]](10)"
    =? [
        info (33, 34) <| K.DuplicateFieldKey(FieldKey.String "x", { start = 22; end' = 23 })
    ]

[<Fact(DisplayName = "`--[[---@type T: { x: string } ]](10)`")>]
let constrainedType() =
    chunkScheme id "return --[[---@type T: { x: string } ]](10)"
    =? scheme1With (types.valueKind, Constraints.ofFields ["x", types.string]) (fun x -> x)

[<Fact(DisplayName = "`--[[---@type { x: number }: { x: string } ]](10)`")>]
let constrainedTypeError() =
    chunkDiagnostics id "return --[[---@type { x: number }: { x: string } ]](10)"
    =? [
        error (20, 33) <| K.UnifyError(TypeMismatch(types.string, types.number))
    ]

[<Fact(DisplayName = "`--[[---@type fun(fun): (fun)]](10)`")>]
let functionTypeAndFunType() =
    let fun' = types.number
    let addFunType = Map.add "fun" <| NonEmptyList.singleton { typeKind = TypeDefinitionKind.Alias fun'; locations = [] }
    chunkScheme (fun c -> { c with withTypeEnv = addFunType })
        "return --[[---@type fun(fun): (fun)]](10)"
    =?
    type0 ([fun'] ->. [fun'])

[<Fact(DisplayName = "`return --[[---@type T]](10), --[[---@type T]](true)`")>]
let localTypeVarEq() =
    chunkScheme id "
    return function()
        return --[[---@type T]](10), --[[---@type T]](true)
    end
    "
    =? type1 (fun a -> [] ->. [a; a])

[<Fact(DisplayName = "`… --[[---@type T]](…) … local function() … --[[---@type T]](…) …`")>]
let globalTypeVarScope() =
    chunkScheme id "
    local x = --[[---@type T]](10)
    local function f() return x, --[[---@type T]](true) end
    return f
    "
    =? type2 (fun a b -> [] ->. [a; b])

[<Fact(DisplayName = "`local function f() … --[[---@type U]](…) … local function g() … --[[---@type U]](…) …`")>]
let localTypeVarScope() =
    chunkScheme id "
    local function f()
        local x = --[[---@type U]](true)
        local function g() return --[[---@type U]]('abc') end
        return x, (g())
    end
    return f
    "
    =? type2 (fun a b -> [] ->. [a; b])

[<Fact(DisplayName = "`--[[---@type fun(fun(...): (...), fun(...): (...), ...): (...)]](…)`")>]
let multiTypeNaming() =
    chunkScheme id "
    return --[[---@type fun(fun(...): (...), fun(...): (...), ...): (...)]](10)
    "
    =?

    // fun(fun(T...): (T...), fun(U...): (U...), V...): (V...)
    type3With (fun c ->
        { c with
            p0 = { c.p0 with kind = types.multiKind }
            p1 = { c.p1 with kind = types.multiKind }
            p2 = { c.p2 with kind = types.multiKind }
        })
        (fun t u v ->
            types.fn(types.fn(t, t)^^types.fn(u, u)^^v, v)
        )

[<Fact(DisplayName = "---@global MyNaN number")>]
let simpleGlobalDeclare() =
    chunkScheme id "
    ---@global MyNaN number
    return MyNaN
    "
    =? Scheme.normalize types.number

[<Fact>]
let globalDeclareScopeError() =
    chunkDiagnostics id "
    local n = MyInf
    local function f()
        ---@global MyInf number
    end
    " =? [
        error (15, 20) <| K.NameNotFound "MyInf"
    ]

[<Fact>]
let emptyBlockGlobalDeclare() =
    chunkScheme id "
    do
        ---@global X string
    end
    return X
    "
    =? types.string

[<Fact>]
let globalDeclareScope() =
    chunkResult id "
    local function f()
        ---@global MyInf number
        return MyInf
    end

    local n = MyInf
    return f(), n

    " =? multi [types.number; types.number]

[<Fact>]
let globalRedeclaration() =
    chunkResult id "
    ---@global MyNaN number
    local x1 = MyNaN
    ---@global MyNaN number
    local x2 = MyNaN
    return x1, x2
    " =? multi [types.number; types.number]

[<Fact>]
let globalRedeclarationError() =
    chunkDiagnostics id "
    ---@global MyNaN number
    ---@global MyNaN string
    " =? [
        error (50, 56) <| K.UnifyError(TypeMismatch(types.number, types.string))
    ]

[<Fact>]
let specialGlobalRedeclarationWarning() =
    chunkDiagnostics id "
    ---@global require _
    "
    =? [
        warning (16, 23) <| K.RedeclarationOfSpecialGlobalVariable("require", DeclarationKind.GlobalRequire, DeclarationKind.NoFeatures)
    ]

[<Fact>]
let globalDeclareTypeParameterScope() =
    chunkResult id "
    ---@global x fun(T): T
    ---@global y fun(T): T
    return x(10), x('a'), y(10), y('a')
    " =? multi [
        types.number
        types.string
        types.number
        types.string
    ]

[<Fact>]
let collisionGlobalVsLocalVariable() =
    chunkResult id "
    local function f()
        local X = 10
        ---@global X string
        return X
    end
    return f(), X
    " =? multi [
        types.number
        types.string
    ]

[<Fact>]
let simpleInterfaceDecl() =
    chunkResult id "
    ---@class Vector2
    ---@field x number
    ---@field y number

    ---@global V2 Vector2
    return V2.x, V2.y
    "
    =? multi [
        types.number
        types.number
    ]

[<Fact>]
let propertyAnnotationOnly() =
    chunkDiagnostics id "
    ---@field f number
    "
    =? [
        info (8, 23) <| K.FieldParentTagNotFound
    ]

[<Fact>]
let isolatedPropertyAnnotation() =
    chunkDiagnostics id "
    ---@class Vec2
    ---@field x number
    local a = 123
    ---@field y number
    "
    =? [
        info (68, 83) K.FieldParentTagNotFound
    ]

[<Fact>]
let emptyInterfaceDecl() =
    chunkScheme id "
    ---@class EmptyInterface
    ---@global X EmptyInterface<number>
    return X
    " =? types.number

[<Fact>]
let noPropertiesInterfaceDeclIsAlias() =
    chunkScheme id "
    ---@class Id : string
    ---@global X Id
    return X
    "
    =? types.string

[<Fact>]
let interfaceDeclScope() =
    chunkScheme id "

    local function f()
      ---@class Id : string
    end

    ---@global X Id
    return X
    "
    =? types.string

[<Fact(DisplayName = "---@class string : { chars: number[] }")>]
let collisionInterfaceDeclVsBasicType() =
    chunkDiagnostics id "
    ---@class string : { chars: number[] }
    "
    =? [
        error (15, 21) <| K.RedeclarationOfBasicType SystemTypeCode.String
    ]

[<Fact>]
let interfaceDeclParentTypeMismatch() =
    chunkDiagnostics id "
    ---@class ParentTypeMismatch : number
    ---@field f1 string
    "
    =? [
        error (60, 66) <| K.UnifyError(UndefinedField(types.number, FieldKey.String "f1"))
    ]

[<Fact>]
let interfaceDeclPropertyTypeMismatch() =
    chunkDiagnostics id "
    ---@class PropertyTypeMismatch : { f1: number }
    ---@field f1 string
    "
    =? [
        error (70, 76) <| K.UnifyError(TypeMismatch(types.number, types.string))
    ]

[<Fact>]
let simpleTypeParam() =
    chunkResult id "
    ---@class Box
    ---@field contents T

    ---@global StringBox Box<string>
    ---@global NumberBox Box<number>
    return StringBox.contents, NumberBox.contents
    "
    =? multi [
        types.string
        types.number
    ]

[<Fact>]
let typeParamScope() =
    chunkResult id "
    ---@class Vector2
    ---@field x T
    ---@field y T

    ---@class Vector4 : Vector2<T>
    ---@field z T
    ---@field w T

    ---@global N2 Vector2<number>
    ---@global S2 Vector2<string>
    ---@global N4 Vector4<number>
    ---@global S4 Vector4<string>

    return N2.x, N2.y, S2.x, S2.y, N4.x, N4.w, S4.x, S4.w
    "
    =?
    let n, s = types.number, types.string
    multi [n; n; s; s; n; n; s; s]

[<Fact>]
let collisionInterfaceDeclVsInterfaceDecl() =
    chunkDiagnostics id "
    ---@class Id : string
    ---@class Bigint : string
    ---@class Bigint : Id
    "
    =? []

[<Fact>]
let collisionInterfaceDeclVsInterfaceDeclTypeMismatch() =
    chunkDiagnostics id "
    ---@class Bigint : string
    ---@class Bigint : number
    "
    =? [
        error (45, 51) <| K.UnifyError(TypeMismatch(types.string, types.number))
    ]

[<Fact>]
let typeParameterShadowingBasicTypeName() =
    chunkScheme id "
    ---@generic number
    ---@class Vector2
    ---@field x number
    ---@field y number

    ---@global S2 Vector2<string>
    return S2.x
    "
    =? types.string

[<Fact(DisplayName = "---@generic Isolated")>]
let isolatedGenericTag() =
    chunkDiagnostics id "
    ---@generic Isolated
    "
    =? [
        info (8, 25) K.GenericTagParentSyntaxNotFound
    ]

[<Fact>]
let typeParameter2() =
    chunkScheme id "
    ---@generic K
    ---@generic V
    ---@class Table : table<K, V>

    ---@global X Table<string, boolean>
    return X
    "
    =? types.table(types.string, types.boolean)

[<Fact>]
let duplicatedTypeParameterUnify() =
    chunkScheme id "
    ---@generic V: { x: N }
    ---@generic V: { y: N }
    ---@generic N
    ---@class Segment2
    ---@field p1 V
    ---@field p2 V

    ---@global Seg Segment2<{ x: number, y: number, z: number }, number>
    return Seg.p1.z
    "
    =? types.number

[<Fact>]
let duplicatedTypeParameterUnifyError() =
    chunkDiagnostics id "
    ---@generic T: { x: string }
    ---@generic T: { x: number }
    ---@class ConstraintTypeMismatch
    "
    =? [
        error (20, 33) <| K.UnifyError(TypeMismatch(types.number, types.string))
    ]

[<Fact>]
let fieldTypeParameterScope() =
    chunkResult id """
    ---@class Utils
    ---@generic T
    ---@field createArray fun(...T): T[]
    ---@generic T
    ---@field id fun(T): T

    ---@global Utils Utils
    local xs1 = Utils.createArray(123, 456)
    local xs2 = Utils.createArray("abc", "dfg")
    local x1 = Utils.id(10)
    local x2 = Utils.id("abc")

    return xs1, xs2, x1, x2
    """
    =? multi [
        types.table(types.number, types.number)
        types.table(types.number, types.string)
        types.number
        types.string
    ]

[<Fact>]
let typeParameterKindMismatch() =
    chunkDiagnostics id "
    ---@generic A
    ---@generic A...
    ---@class TypeParameterKindMismatch
    "
    =? [
        error (35, 36) <| K.UnifyError(KindMismatch(types.valueKind, types.multiKind))
    ]

[<Fact>]
let typeVariableKindMismatch() =
    chunkDiagnostics id "
    ---@generic V...
    ---@class TypeVariableKindMismatch
    ---@field ignore fun(V): ()
    "
    =? [
        error (86, 87) DiagnosticKind.UnexpectedMultiType
    ]

[<Fact>]
let typeParameterScope() =
    chunkResult id "
    ---@generic Number
    ---@class Operations
    ---@field eq fun(Number, Number): TBool
    ---@generic Any
    ---@field eqAny fun(Number, Any): TBool

    ---@global Ops Operations<number, boolean>

    local x1 = Ops.eq(10, 20)
    local x2 = Ops.eqAny(10, 20)
    local x3 = Ops.eqAny(10, 'abc')
    return x1, x2, x3
    "
    =? multi [
        types.boolean
        types.boolean
        types.boolean
    ]

[<Fact>]
let multiTypeParameterScope() =
    chunkResult id "
    ---@class Utils
    ---@generic T...
    ---@field id fun(T...): (T...)

    ---@global Utils Utils
    return Utils.id(1), Utils.id('a', true)
    "
    =? multi [
        types.number
        types.string
        types.boolean
    ]

[<Fact>]
let typeTagWithGenericTag() =
    chunkResult id "
    local getX = --[[---@generic T: { x: X }, X @type fun(T): X]](42)
    return getX { x = 10, y = 20 }, getX { x = '?', men = true }
    "
    =? multi [
        types.number
        types.string
    ]

[<Fact>]
let typeAbstractionAnnotation() =
    chunkResult id "
    local id = --[[---@generic T @type fun(T): T]](42)
    local id2 = --[[---@generic T @type fun(T): T]](42)
    return id('a'), id(7), id2('a'), id2(7)
    "
    =? multi [
        types.string
        types.number
        types.string
        types.number
    ]

[<Fact>]
let typeVariableAnnotation() =
    chunkScheme id "
    local id = --[[---@type fun(T): T]](42)
    local x1 = id('a')
    local x2 = id(7)
    return id
    "
    =? scheme1With (types.valueKind, Constraints.tagOrUpper (TagSpace.ofNumbers [7.] + TagSpace.ofStrings ["a"])) (fun a ->
        [a] ->. [a]
    )

[<Fact>]
let globalTagWithGenericTag() =
    chunkResult id "
    ---@generic Args...
    ---@global id fun(Args...): Args...

    local x1 = id(10)
    local x2, x3 = id(true, 'abc')
    return x1, x2, x3
    "
    =? multi [
        types.number
        types.boolean
        types.string
    ]

[<Fact>]
let recursiveClassDefinition() =
    // Animal = type ('self: { greet: fun('self): string }). 'self
    chunkDiagnostics id "
    ---@class Animal
    ---@field greet fun(self): string
    ---@global printGreet fun(Animal<_>): ()

    printGreet {
        name = 'dog',
        greet = function(self) return 'My name is ' .. self.name end
    }
    "
    =? []

[<Fact>]
let recursiveClassDefinitionError() =
    chunkDiagnostics id "
    ---@class Animal
    ---@field greet fun(self): string
    ---@global printGreet fun(Animal<_>): ()

    printGreet {
        greet = function(self) return 'My name is ' .. self.name end
    }
    "
    =? List.map Diagnostic.normalize [
        RequireField(
            Map [
                FieldKey.String "greet", scheme1With (types.valueKind, Constraints.ofFields ["name", types.string]) <| fun t1 -> [t1] ->. [types.string]
            ],
            FieldKey.String "name",
            types.string
        )
        |> K.UnifyError
        |> error (121, 197)
    ]

[<Fact>]
let recursiveClassDefinitionError2() =
    chunkDiagnostics id "
    ---@class Animal
    ---@field greet fun(self): string
    ---@global printGreet fun(Animal<_>): ()

    printGreet {
        name = 'dog',
        greet_ = function(self) return 'My name is ' .. self.name end
    }
    "
    =? [
        RequireField(
            Map [
                FieldKey.String "greet_", scheme1With (types.valueKind, Constraints.ofFields ["name", types.string]) <| fun t1 -> [t1] ->. [types.string]
                FieldKey.String "name", types.string
            ],
            // fun(?5026204(1): { greet: fun(rec ?5026204): string; }): string
            FieldKey.String "greet", forall1 <| fun t1 -> Constraints.ofFields ["greet", [t1] ->. [types.string]], [t1] ->. [types.string]
        )
        |> K.UnifyError
        |> error (121, 220)
    ]

[<Fact>]
let recursiveClassDefinitionError3() =
    chunkDiagnostics id "
    ---@class Animal
    ---@field greet fun(self): string
    ---@global printGreet fun(Animal<_>): ()

    printGreet {
        name = 123,
        greet = function(self) return 'My name is ' .. self.name end
    }
    "
    =? [
        error (121, 217) <| K.UnifyError(ConstraintMismatch(Constraints.tagOrLower TagSpace.allString, Constraints.numberOrUpper 123.))
    ]

let shapesSource = "
    ---@class Shape
    ---@field contains fun(Shape, x: number, y: number): boolean
    ---@field area fun(self): number

    ---@class Polygon : Shape<_>
    ---@field vertexCount fun(self): number
    ---@field vertex fun(self, i: number): (x: number, y: number)

    ---@global printShape fun(Shape<_>): ()
    ---@global printPolygon fun(Polygon<_>): ()

    local circle = {
        _r = 4,
        contains = function(self, x, y)
            return (x * x + y * y) <= (self._r * self._r)
        end,
        area = function(self)
            return self._r * self._r * 3.14159265
        end
    }
    local rect = {
        _w = 2,
        _h = 3,
        contains = function(self, x, y)
            return
                0 <= x and x <= self._w and
                0 <= y and y <= self._h
        end,
        area = function(self) return self._w * self._h end,
        vertexCount = function(self) return 4 end,
        vertex = function(self, i)
            if i == 1 then
                return self._w, self._h
            --[[ … ]]
            else
                return 0, 0
            end
        end,
    }
    local dog = { name = 'dog' }
"

[<Fact>]
let recursiveClassExtend() =
    shapesSource + "
    printShape(circle)
    printShape(rect)
    printPolygon(rect)
    "
    |> chunkDiagnostics id =? []

[<Fact>]
let recursiveClassExtendError() =
    shapesSource + "
    printPolygon(circle)
    "
    |> chunkDiagnostics id =? [
        let number = types.number
        let boolean = types.boolean

        RequireField(
            Map [
                FieldKey.String "_r", number
                FieldKey.String "area", scheme1With (types.valueKind, Constraints.ofFields ["_r", number]) <| fun t0 -> [t0] ->. [number]
                FieldKey.String "contains", scheme1With (types.valueKind, Constraints.ofFields ["_r", number]) <| fun t0 -> [t0; number; number] ->. [boolean]
            ],
            FieldKey.String "vertex",

            // type ('polygon: { _r: …, vertex: …, … }). fun('polygon, i: number): (x: number, y: number)
            forall1 <| fun polygon ->
                let polygonC = Constraints.ofFields [
                    "_r", number
                    "area", [polygon] ->. [number]
                    "contains", [polygon; number; number] ->. [boolean]
                    "vertex", [polygon; number] ->. [number; number]
                    "vertexCount", [polygon] ->. [number]
                ]
                polygonC, [polygon; number] ->. [number; number]
        )
        |> K.UnifyError
        |> error (1179, 1187)
    ]

[<Fact>]
let recursiveClassExtendError2() =
    shapesSource + "
    printShape(dog)
    "
    |> chunkDiagnostics id =? [
        let string = types.string
        let number = types.number
        let boolean = types.boolean

        RequireField(
            Map [
                FieldKey.String "name", string
            ],
            FieldKey.String "area",

            // type ('0: { area: fun('0): number; contains: fun('0, number, number): boolean; }). fun('0): number
            forall1 <| fun t0 ->
                let c0 = Constraints.ofFields [
                    "area", [t0] ->. [number]
                    "contains", [t0; number; number] ->. [boolean]
                ]
                c0, [t0] ->. [number]
        )
        |> K.UnifyError
        |> error (1177, 1182)
    ]

[<Fact>]
let recursiveClassExtendError3() =
    shapesSource + "
    printPolygon(dog)
    "
    |> chunkDiagnostics id =? [
        let string = types.string
        let number = types.number
        let boolean = types.boolean

        RequireField(
            Map [
                FieldKey.String "name", string
            ],
            FieldKey.String "area",
            forall1 <| fun t0 ->
                let c0 = Constraints.ofFields [
                    "area", [t0] ->. [number]
                    "contains", [t0; number; number] ->. [boolean]
                    "vertex",  [t0; number] ->. [number; number]
                    "vertexCount", [t0] ->. [number]
                ]
                c0, [t0] ->. [number]
        )
        |> K.UnifyError
        |> error (1179, 1184)
    ]

[<Fact>]
let treatUnresolvedVoidAsEmptyType() =
    chunkResult id "
    ---@global f fun(): void
    return f()
    "
    =? types.empty

[<Fact>]
let scopedVoidAsEmptyType() =
    chunkResult id "
    ---@class void : string
    ---@global f fun(): void
    return f()
    "
    =? multi [types.string]

[<Fact>]
let typeVarInMultiConstraint() =
    chunkScheme id "
    ---@class Utils
    ---@generic T
    ---@field count fun(...T): number

    ---@global Utils Utils

    return Utils
    "
    =? Type.interfaceType [
        "count", type1 <| fun t ->
            types.fn(
                MultiType.newVarWith 1 (ValueSome(MultiElementTypeConstraint t |> withEmptyLocation)),
                types.multi1 types.number
            )
    ]
