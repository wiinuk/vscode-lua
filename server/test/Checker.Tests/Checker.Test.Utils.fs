module LuaChecker.Checker.Test.Utils
open FsCheck
open LuaChecker
open LuaChecker.Primitives
open LuaChecker.Syntaxes
open LuaChecker.Syntax
open System


let (=?) l r = if not (l = r) then failwithf "%A =? %A" l r
let (<>?) l r = if not (l <> r) then failwithf "%A <>? %A" l r

type private K = Syntax.TokenKind
module Token =
    let token k = { trivia = Trivia.createEmpty(); kind = k }
    let name value = token <| K.Name value
    let nil<'a> : Token<_,Trivia<'a>> = token K.Nil
    let bool value = token <| if value then K.True else K.False
    let number value = token <| K.Number value
    let string value = token <| K.String value

let headChars = List.concat [ ['a'..'z']; ['A'..'Z']; ['_'] ]
let tailChars = List.concat [ headChars; ['0'..'9'] ] // Gen.elements

[<RequireQualifiedAccess>]
type Precedence =
    | Or
    | And
    | Rel
    | Con
    | Add
    | Mul
    | Unary
    | Pow
    | Prim

let precedence = function
    | BinaryOpKind.Or -> Precedence.Or
    | BinaryOpKind.And -> Precedence.And
    | BinaryOpKind.Lt
    | BinaryOpKind.Gt
    | BinaryOpKind.Le
    | BinaryOpKind.Ge
    | BinaryOpKind.Eq
    | BinaryOpKind.Ne -> Precedence.Rel
    | BinaryOpKind.Con -> Precedence.Con
    | BinaryOpKind.Add
    | BinaryOpKind.Sub -> Precedence.Add
    | BinaryOpKind.Mul
    | BinaryOpKind.Div
    | BinaryOpKind.Mod -> Precedence.Mul
    | BinaryOpKind.Pow -> Precedence.Pow

type Associativity =
    | Left
    | Right

let assoc = function
    | BinaryOpKind.Or
    | BinaryOpKind.And
    | BinaryOpKind.Lt
    | BinaryOpKind.Gt
    | BinaryOpKind.Le
    | BinaryOpKind.Ge
    | BinaryOpKind.Eq
    | BinaryOpKind.Ne
    | BinaryOpKind.Add
    | BinaryOpKind.Sub
    | BinaryOpKind.Mul
    | BinaryOpKind.Div
    | BinaryOpKind.Mod -> Associativity.Left
    | BinaryOpKind.Con
    | BinaryOpKind.Pow -> Associativity.Right

let (|Precedence|) = function
    | Binary(_, { kind = k }, _) -> precedence k
    | Literal _
    | VarArg _
    | Function _
    | PrefixExp _
    | NewTable _ -> Precedence.Prim
    | Unary _ -> Precedence.Unary

let (|Assoc|) { kind = k } = assoc k

let ks =
    seq {
        for c in Reflection.FSharpType.GetUnionCases typeof<TokenKind> do
            if c.GetFields().Length = 0 then
                let k = Reflection.FSharpValue.MakeUnion(c, null) :?> TokenKind
                if TokenKind.Unknown <> k then c.Tag, k
    }
    |> Seq.sortBy fst
    |> Seq.map snd
    |> Seq.toArray

let intToKind n = ks.[abs n % ks.Length]
let kindToInt =
    ks
    |> Seq.mapi (fun i k -> k, i)
    |> Map.ofSeq

type ValidName = ValidName of string
type PositiveNormalFloat = PositiveNormalFloat of double
module D = Documents

module Arb =
    let convertRec scaleSize convertFromLeaf leafArb convertFrom convertTo deepArb =
        let generator = Gen.sized <| fun size ->
            if size = 0 then
                Arb.toGen leafArb |> Gen.scaleSize scaleSize |> Gen.map convertFromLeaf
            else
                Arb.toGen deepArb |> Gen.scaleSize scaleSize |> Gen.map convertFrom

        let shrinker x = seq {
            for x in Arb.toShrink deepArb <| convertTo x do
                yield convertFrom x
        }
        Arb.fromGenShrink(generator, shrinker)

type Arbs =
    static member Trivia(): 'D Trivia Arbitrary =
        Arb.convertRec
            (fun x -> x / 2)
            Trivia.createEmpty
            Arb.from

            (fun (x1, x2, x3) -> { leadingTriviaLength = x1; leadingDocument = None; span = x2; trailingTriviaLength = x3; trailingDocument = None })
            (fun x -> x.leadingTriviaLength, x.span, x.trailingTriviaLength)
            Arb.from

    static member Block'() =
        Arb.convertRec
            (fun x -> x / 5)

            (fun () -> { stats = []; lastStat = None })
            Arb.from

            (fun (xs, x) -> { stats = xs; lastStat = x } )
            (fun x -> x.stats, x.lastStat)
            Arb.from

    static member Stat'() =
        Arb.convertRec
            (fun x -> x / 10)

            (fun (x1, x2) -> Local(Token.token HEmpty, x1, x2))
            Arb.from

            (function
            | Choice1Of7 x -> FunctionCall x
            | Choice2Of7(x1, x2, x3) -> Assign(x1, x2, x3)
            | Choice3Of7(x1, x2, x3) -> Do(x1, x2, x3)
            | Choice4Of7(x1, x2, x3, x4, x5) -> While(x1, x2, x3, x4, x5)
            | Choice5Of7(x1, x2, x3, x4) -> RepeatUntil(x1, x2, x3, x4)
            | Choice6Of7(x1, x2, x3, x4, x5, x6, x7) -> If(x1, x2, x3, x4, x5, x6, x7)
            | Choice7Of7(Choice1Of5(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10)) -> For(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10)
            | Choice7Of7(Choice2Of5(x1, x2, x3, x4, x5, x6, x7)) -> ForIn(x1, x2, x3, x4, x5, x6, x7)
            | Choice7Of7(Choice3Of5(x1, x2, x3)) -> FunctionDecl(x1, x2, x3)
            | Choice7Of7(Choice4Of5(x1, x2, x3, x4)) -> LocalFunction(x1, x2, x3, x4)
            | Choice7Of7(Choice5Of5(x1, x2, x3)) -> Local(x1, x2, x3)
            )
            (function
            | FunctionCall x -> Choice1Of7 x
            | Assign(x1, x2, x3) -> Choice2Of7(x1, x2, x3)
            | Do(x1, x2, x3) -> Choice3Of7(x1, x2, x3)
            | While(x1, x2, x3, x4, x5) -> Choice4Of7(x1, x2, x3, x4, x5)
            | RepeatUntil(x1, x2, x3, x4) -> Choice5Of7(x1, x2, x3, x4)
            | If(x1, x2, x3, x4, x5, x6, x7) -> Choice6Of7(x1, x2, x3, x4, x5, x6, x7)
            | For(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) -> Choice7Of7(Choice1Of5(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10))
            | ForIn(x1, x2, x3, x4, x5, x6, x7) -> Choice7Of7(Choice2Of5(x1, x2, x3, x4, x5, x6, x7))
            | FunctionDecl(x1, x2, x3) -> Choice7Of7(Choice3Of5(x1, x2, x3))
            | LocalFunction(x1, x2, x3, x4) -> Choice7Of7(Choice4Of5(x1, x2, x3, x4))
            | Local(x1, x2, x3) -> Choice7Of7(Choice5Of5(x1, x2, x3))
            )
            Arb.from

    static member PositiveNormalFloat() =
        Arb.from
        |> Arb.convert
            (fun (NormalFloat x) -> PositiveNormalFloat(abs x))
            (fun (PositiveNormalFloat x) -> NormalFloat x)

    static member ValidName() =
        let g = gen {
            let! head = Gen.elements headChars
            let! tail = Gen.arrayOf <| Gen.elements tailChars
            return Array.append [|head|] tail |> String
        }
        let g = gen {
            let! name = Gen.filter Name.isValid g
            return ValidName name
        }
        let shrink (ValidName x) = seq {
            for x in Arb.shrink x do
                if Name.isValid x then
                    ValidName x
        }
        Arb.fromGenShrink(g, shrink)

    static member Name() =
        Arb.from
        |> Arb.convert
            (fun (ValidName x, t) -> Name { kind = x; trivia = t })
            (fun (Name x) -> ValidName x.kind, x.trivia)

    static member Comment() =
        Arb.from
        |> Arb.convert
            (fun (NonNull x, t) -> Documents.Comment { kind = x; trivia = t })
            (fun (Documents.Comment x) -> NonNull x.kind, x.trivia)

    static member StringLiteral() =
        Arb.from
        |> Arb.convert
            (fun (t, NonNull k) -> StringLiteral { trivia = t; kind = k })
            (fun (StringLiteral t) -> t.trivia, NonNull t.kind)

    static member LiteralKind() =
        Arb.from
        |> Arb.convert (function
        | Choice1Of3 None -> Nil
        | Choice1Of3(Some false) -> False
        | Choice1Of3(Some true) -> True
        | Choice2Of3(PositiveNormalFloat x) -> Number x
        | Choice3Of3(NonNull x) -> LiteralKind.String x
        ) (function
        | Nil -> Choice1Of3 None
        | False -> Choice1Of3(Some false)
        | True -> Choice1Of3(Some true)
        | Number x -> Choice2Of3(PositiveNormalFloat x)
        | LiteralKind.String x -> Choice3Of3(NonNull x)
        )

    static member TokenKind() =
        Arb.from
        |> Arb.convert
            (function
            | Choice1Of4 x -> intToKind x
            | Choice2Of4(PositiveNormalFloat x) -> TokenKind.Number x
            | Choice3Of4(NonNull x) -> TokenKind.String x
            | Choice4Of4(ValidName x) -> TokenKind.Name x
            )
            (function
            | TokenKind.Number x -> Choice2Of4(PositiveNormalFloat x)
            | TokenKind.String x -> Choice3Of4(NonNull x)
            | TokenKind.Name x -> Choice4Of4(ValidName x)
            | k -> Choice1Of4 kindToInt.[k]
            )

    static member Exp() =
        Arb.Default.Derive()
        |> Arb.filter (function
            // (a, '*', (b, '+', c))
            // ((a, '+', b), '*', c)
            | Binary({ kind = Precedence l }, _, { kind = Precedence r }) & Precedence p when r < p || l < p -> false
            // ('-', (a, '+', b))
            | Unary(_, { kind = Precedence u }) & Precedence p when u < p -> false
            // (a, '+', (b, '+', c))
            | Binary(_, Assoc Left, { kind = Binary(_, Assoc Left, _) & Precedence r }) & Precedence p when p = r -> false
            // ((a, '^', b), '^', c)
            | Binary({ kind = Binary(_, Assoc Right, _) & Precedence l }, Assoc Right, _) & Precedence p when p = l -> false
            | _ -> true
        )

    static member FieldKey() =
        Arb.from
        |> Arb.convert
            (function
            | Choice1Of3(NonNull x) -> FieldKey.String x
            | Choice2Of3(NormalFloat x) -> FieldKey.Number x
            | Choice3Of3 x -> FieldKey.Bool x
            )
            (function
            | FieldKey.String x -> Choice1Of3(NonNull x)
            | FieldKey.Number x -> Choice2Of3(NormalFloat x)
            | FieldKey.Bool x -> Choice3Of3 x
            )

    static member TypeSign'() =
        let generator =
            let span = Arb.generate<Span>
            let fieldKey = Arb.generate<FieldKey Source>
            let typeSign scale = Gen.scaleSize scale Arb.generate<D.TypeSign>
            let name = Arb.generate<D.Name>
            let positiveInt = Arb.generate<PositiveInt>
            let nonNegativeInt = Arb.generate<NonNegativeInt>

            let withSpan kind = gen {
                let! k = kind
                let! s = span
                return { kind = k; trivia = s }
            }
            let leafType = gen {
                let! name = name
                return D.NamedType(name, [])
            }
            let namedType = gen {
                let! name = name
                let! PositiveInt arity = positiveInt
                let! types = Gen.listOfLength arity (typeSign <| fun s -> s / arity)
                return D.NamedType(name, types)
            }
            let field = withSpan <| gen {
                let! k = fieldKey
                let! t = typeSign <| fun s -> max 0 (s - 1)
                return D.Field(k, t)
            }
            let fields = withSpan <| gen {
                let! PositiveInt fieldCount = positiveInt
                let! fields = Gen.listOfLength fieldCount (Gen.scaleSize (fun s -> s / fieldCount) field)
                return D.Fields(NonEmptyList(List.head fields, List.tail fields))
            }
            let interfaceType = gen {
                let! fields = fields
                return D.InterfaceType fields
            }
            let arrayType = gen {
                let! t = typeSign <| fun s -> max 0 (s - 1)
                return D.ArrayType t
            }
            let constrainedType = gen {
                let! t = typeSign <| fun s -> s / 2
                let! fs = Gen.scaleSize (fun s -> s / 2) fields
                return D.ConstrainedType(t, fs)
            }
            let parameter = withSpan <| gen {
                let! n = Gen.optionOf name
                let! t = typeSign <| fun s -> max 0 (s - 1)
                return D.Parameter(n, t)
            }
            let variadicParameter = withSpan <| gen {
                let! n = Gen.optionOf name
                let! c = Gen.optionOf <| typeSign (fun s -> s / 2)
                return D.VariadicParameter(n, c)
            }
            let multiType = gen {
                let! NonNegativeInt parameterCount = nonNegativeInt
                let! ps = Gen.listOfLength parameterCount (Gen.scaleSize (fun s -> if parameterCount = 0 then 0 else s / parameterCount) parameter)
                let! v = Gen.optionOf variadicParameter
                return D.MultiType(ps, v)
            }
            let functionType = gen {
                let! m1 = Gen.scaleSize (fun s -> s / 2) multiType
                let! s1 = span
                let! m2 = Gen.scaleSize (fun s -> s / 2) multiType
                let! s2 = span
                return D.FunctionType({ kind = m1; trivia = s1 }, { kind = m2; trivia = s2 })
            }
            let typeSign' = function
                | 0 -> leafType
                | _ ->
                Gen.oneof [
                    leafType
                    Gen.oneof [
                        namedType
                        interfaceType
                        arrayType
                        constrainedType
                        functionType
                    ]
                ]
            Gen.sized typeSign'

        let shrink = Arb.Default.Derive().Shrinker
        Arb.fromGenShrink(generator, shrink)

let checkConfig = {
    Config.QuickThrowOnFailure with
        Arbitrary = [typeof<Arbs>]
        QuietOnSuccess = true
}
let check test = Check.One(checkConfig, test)

let outputRaiseOnFailureRunner output = { new IRunner with
    member _.OnStartFixture t =
        Runner.onStartFixtureToString t |> output

    member _.OnArguments(count, args, every) =
        every count args |> output

    member _.OnShrink(args, everyShrink) =
        everyShrink args |> output

    member _.OnFinished(name, testResult) =
        Runner.onFinishedToString name testResult |> output
        match testResult with
        | TestResult.True _ -> ()
        | _ -> failwithf "%s" <| Runner.onFinishedToString name testResult
}
let checkWith withConfig test = Check.One(withConfig checkConfig, test)
