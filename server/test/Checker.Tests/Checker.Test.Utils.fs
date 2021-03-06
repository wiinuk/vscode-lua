module LuaChecker.Checker.Test.Utils
open FsCheck
open LuaChecker
open LuaChecker.Primitives
open LuaChecker.Syntaxes
open LuaChecker.Syntax
open System
module D = DocumentPrinter


type private K = Syntax.TokenKind

module SepBy =
    let toList (SepBy(x, sepXs)) = x::List.map snd sepXs

module Name =
    let map mapping (Name x) = Name <| Token.map mapping x

module private rec MapRec =
    let inline option f = function None -> None | Some x -> Some(f x)
    let inline tuple2 (f1, f2) (x1, x2) = f1 x1, f2 x2
    let inline trivial map (mapSpan: Span -> Span, (mapTrivia: Trivia -> Trivia)) x = { kind = map (mapSpan, mapTrivia) x.kind; trivia = mapSpan x.trivia }

    let token (_, f) x = Token.map f x
    let name (_, f) x = Name.map f x
    let nameList f x = trivial (fun f x -> SepBy.mapSep (token f) (name f) x) f x

    let exp f x = trivial exp' f x
    let exp' f = function
        | Literal x -> Literal <| token f x
        /// `...´
        | VarArg x -> VarArg <| token f x
        | Function(x1, x2) -> Function(token f x1, funcBody f x2)
        | PrefixExp x -> PrefixExp <| prefixExp f x
        | NewTable x -> NewTable <| tableConstructor f x
        | Binary(x1, x2, x3) -> Binary(exp f x1, token f x2, exp f x3)
        | Unary(x1, x2) -> Unary(token f x1, exp f x2)

    let expList f x = trivial (fun f x -> SepBy.mapSep (token f) (exp f) x) f x

    let var f x = trivial var' f x
    let var' f = function
        | Variable x -> Variable <| name f x
        | Index(x1, x2, x3, x4) -> Var'.Index(prefixExp f x1, token f x2, exp f x3, token f x4)
        | Member(x1, x2, x3) -> Member(prefixExp f x1, token f x2, name f x3)

    let args f x = trivial args' f x
    let args' f = function
        | Args(x1, x2, x3) -> Args(token f x1, option (expList f) x2, token f x3)
        | StringArg(StringLiteral x) -> StringArg <| StringLiteral(token f x)
        | TableArg x -> TableArg <| tableConstructor f x

    let functionCall f x = trivial functionCall' f x
    let functionCall' f = function
        | Call(x1, x2) -> Call(prefixExp f x1, args f x2)
        | CallWithSelf(x1, x2, x3, x4) -> CallWithSelf(prefixExp f x1, token f x2, name f x3, args f x4)

    let prefixExp f x = trivial prefixExp' f x
    let prefixExp' f = function
        | Apply x -> Apply <| functionCall f x
        | Var x -> Var <| var f x
        | Wrap(x1, x2, x3) -> Wrap(token f x1, exp f x2, token f x3)

    let varList f x = trivial (fun f x -> SepBy.mapSep (token f) (var f) x) f x

    let field f x = trivial field' f x
    let field' f = function
        | Init x -> Init <| exp f x
        | IndexInit(x1, x2, x3, x4, x5) -> IndexInit(token f x1, exp f x2, token f x3, token f x4, exp f x5)
        | MemberInit(x1, x2, x3) -> MemberInit(name f x1, token f x2, exp f x3)

    let fieldList f (FieldList(x1, x2)) = FieldList(SepBy.mapSep (token f) (field f) x1, option (token f) x2)
    let tableConstructor f x = trivial tableConstructor' f x
    let tableConstructor' f (TableConstructor(x1, x2, x3)) =
        TableConstructor(token f x1, option (fieldList f) x2, token f x3)

    let parameterList f x = trivial parameterList' f x
    let parameterList' f = function
        | ParameterList(x1, x2) -> ParameterList(nameList f x1, option (tuple2 (token f, token f)) x2)
        | VarParameter x -> VarParameter(token f x)

    let funcBody f x = trivial funcBody' f x
    let funcBody' f (FuncBody(x1, x2, x3, x4, x5)) =
        FuncBody(token f x1, option (parameterList f) x2, token f x3, block f x4, token f x5)

    let funcName f x = trivial funcName' f x
    let funcName' f (FuncName(x1, x2, x3)) =
        FuncName(name f x1, List.map (tuple2(token f, name f)) x2, option (tuple2(token f, name f)) x3)

    let elseIfClause f x = trivial elseIfClause' f x
    let elseIfClause' f (ElseIf(x1, x2, x3, x4)) = ElseIf(token f x1, exp f x2, token f x3, block f x4)
    let elseClause f x = trivial elseClause' f x
    let elseClause' f (Else(x1, x2)) = Else(token f x1, block f x2)

    let stat f x = trivial stat' f x
    let stat' f = function
        | Assign(x1, x2, x3) -> Assign(varList f x1, token f x2, expList f x3)
        | FunctionCall x -> FunctionCall <| functionCall f x
        | Do(x1, x2, x3) -> Do(token f x1, block f x2, token f x3)
        | While(x1, x2, x3, x4, x5) -> While(token f x1, exp f x2, token f x3, block f x4, token f x5)
        | RepeatUntil(x1, x2, x3, x4) -> RepeatUntil(token f x1, block f x2, token f x3, exp f x4)
        | If(x1, x2, x3, x4, x5, x6, x7) ->
            If(
                token f x1, exp f x2, token f x3, block f x4,
                List.map (elseIfClause f) x5, option (elseClause f) x6, token f x7
            )
        | For(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) ->
            For(
                token f x1, name f x2, token f x3, exp f x4, token f x5, exp f x6,
                option (tuple2(token f, exp f)) x7,
                token f x8, block f x9, token f x10
            )
        | ForIn(x1, x2, x3, x4, x5, x6, x7) ->
            ForIn(token f x1, nameList f x2, token f x3, expList f x4, token f x5, block f x6, token f x7)

        | FunctionDecl(x1, x2, x3) -> FunctionDecl(token f x1, funcName f x2, funcBody f x3)
        | LocalFunction(x1, x2, x3, x4) -> LocalFunction(token f x1, token f x2, name f x3, funcBody f x4)
        | Local(x1, x2, x3) -> Local(token f x1, nameList f x2, option (tuple2(token f, expList f)) x3)

    let lastStat f x = trivial lastStat' f x
    let lastStat' f = function
        | Break x -> Break <| token f x
        | Return(x1, x2) -> Return(token f x1, option (expList f) x2)

    let block ((_, mapTrivia) as f) x = {
        kind = block' f x.kind
        trivia = mapTrivia x.trivia
    }

    let block' f x = {
        stats = List.map (tuple2(stat f, option (token f))) x.stats
        lastStat = option (tuple2(lastStat f, option (token f))) x.lastStat
    }

module Exp =
    let map mapping x = MapRec.exp mapping x

module Var =
    let map mapping x = MapRec.var mapping x

module Stat =
    let map mapping x = MapRec.stat mapping x

module Block =
    let map mapping x = MapRec.block mapping x

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Trivia =
    let createEmpty() = {
        leadingTriviaLength = 0
        leadingDocument = None
        span = Span.empty
        trailingTriviaLength = 0
        trailingDocument = None
    }

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

    static member TypeSign'<'A>() =
        let generator =
            let annotation = Arb.generate<'A>

            /// empty
            let trivia = Gen.fresh Trivia.createEmpty
            /// empty
            let span = Gen.constant Span.empty
            /// empty
            let reserved = gen {
                let! annotation = annotation
                return D.Annotated({ trivia = Span.empty; kind = HEmpty }, annotation)
            }
            let annotated x = gen {
                let! x = x
                let! annotation = annotation
                return D.Annotated(x, annotation)
            }
            let fieldKey = Arb.generate<FieldKey Source>
            let fieldIdentifier = annotated fieldKey
            let name = Arb.generate<HEmpty Syntax.Name>
            let identifier = annotated name
            let fieldSepKind = Arb.generate<FieldSepKind>
            let positiveInt = Arb.generate<PositiveInt>

            let withSpan' kind = gen {
                let! k = kind
                let! s = span
                return { kind = k; trivia = s }
            }
            let withSpan kind = withSpan' (Gen.constant kind)
            let fieldSep = gen {
                let! sep = fieldSepKind
                let! trivia = span
                let! annotation = annotation
                return D.Annotated({ kind = sep; trivia = trivia }, annotation)
            }
            let wrap t = gen {
                let! l = reserved
                let! r = reserved
                return D.WrappedType(l, t, r)
            }
            let rec typeSignNoWrap' size =
                if size <= 0 then leafType else

                Gen.oneof [
                    leafType
                    Gen.frequency [
                        8, namedType size
                        8, interfaceType size
                        8, arrayType size
                        8, constrainedType size
                        8, functionType size
                        8, emptyMultiType size
                        8, singleMultiType size
                        8, variadicType size
                        8, multiType2 size
                        1, wrappedType size
                    ]
                ]

            and typeSignNoWrap size = gen {
                let! t = typeSignNoWrap' size
                let! span = span
                return { kind = t; trivia = span }
                }
            and typeSignOrWrap minPrecedence scale = gen {
                let! t = typeSignNoWrap scale
                if DocumentPrinter.typePrecedence t.kind < minPrecedence
                then return! withSpan' <| wrap t
                else return t
                }

            and wrappedType size = gen {
                let! t = typeSignOrWrap D.Precedence.Max (max 0 (size - 1))
                return! wrap t
                }
            and sepByOfLength length sep x = gen {
                if length < 1 then invalidArg (nameof length) $"{length} < 1"

                let! x0 = x
                let! sepXs = Gen.listOfLength (length - 1) (Gen.zip sep x)
                return SepBy(x0, sepXs)
                }
            and leafType = Gen.frequency [
                7, gen {
                    let! n = identifier
                    return D.NamedType(n, None)
                }
                1, gen {
                    let! r = reserved
                    return D.NilType r
                }
                ]
            and genericArguments size = gen {
                match size with
                | 0 -> return None
                | _ ->

                let! PositiveInt randomN = positiveInt
                let arity = max 1 (randomN % (size + 1))
                let! lt = reserved
                let! ps = sepByOfLength arity reserved (typeSignOrWrap D.Precedence.ConstrainedType (size / arity))
                let! comma = Gen.optionOf reserved
                let! gt = reserved
                return Some(D.GenericArguments(lt, ps, comma, gt))
                }
            and namedType size = gen {
                let! n = identifier
                let! genericArguments = genericArguments (max 0 (size - 1))
                return D.NamedType(n, genericArguments)
                }
            and field size = withSpan' <| gen {
                let! k = fieldIdentifier
                let! colon = reserved
                let! t = typeSignOrWrap D.Precedence.ConstrainedType (max 0 (size - 1))
                return D.Field(k, colon, t)
                }
            and fields size = withSpan' <| gen {
                let! PositiveInt randomN = positiveInt
                let fieldCount = max 1 (randomN % (size + 1))
                let! lcBracket = reserved
                let! fields = sepByOfLength fieldCount fieldSep (field (size / fieldCount))
                let! fieldSep = Gen.optionOf fieldSep
                let! rcBracket = reserved
                return D.Fields(lcBracket, fields, fieldSep, rcBracket)
                }
            and interfaceType size = gen {
                let! fields = fields size
                return D.InterfaceType fields
                }
            and arrayType size = gen {
                let! t = typeSignOrWrap D.Precedence.ArrayType (max 0 (size - 1))
                let! lsBracket = reserved
                let! rsBracket = reserved
                return D.ArrayType(t, lsBracket, rsBracket)
                }
            and constrainedType size = gen {
                let! t = typeSignOrWrap D.Precedence.ArrayType (size / 2)
                let! colon = reserved
                let! fs = fields (size / 2)
                return D.ConstrainedType(t, colon, fs)
                }
            and parameter size = Gen.oneof [
                withSpan' <| gen {
                    let! t = typeSignOrWrap D.Precedence.FunctionType (max 0 (size - 1))
                    return D.Parameter(None, t)
                }
                withSpan' <| gen {
                    let! n = Gen.zip identifier reserved
                    let! t = typeSignOrWrap D.Precedence.ConstrainedType (max 0 (size - 1))
                    return D.Parameter(Some n, t)
                    }
                ]
            and variadicTypeSign size = gen {
                let! n = Gen.optionOf identifier
                let! dot3 = reserved
                let! c = Gen.optionOf <| typeSignOrWrap D.Precedence.PrimitiveType (max 0 (size - 1))
                let! v = withSpan <| D.VariadicTypeSign(n, dot3, c)
                return v
                }
            and variadicType size = gen {
                let! v = variadicTypeSign size
                return D.VariadicType v
                }
            and emptyMultiType _ = gen {
                let! l = reserved
                let! r = reserved
                return D.EmptyType(l, r)
                }
            and singleMultiType size = gen {
                let! l = reserved
                let! p = parameter size
                let! comma = reserved
                let! r = reserved
                return D.SingleMultiType(l, p, comma, r)
                }
            and parameters1 size = gen {
                let! PositiveInt parameterCount = positiveInt
                let! ps = sepByOfLength parameterCount reserved (parameter (size / parameterCount))
                return D.Parameters ps
                }
            and multiType2 size = gen {
                let! p = parameter (size / 2)
                let! comma = reserved
                let! ps = parameters1 (size / 2)
                return D.MultiType2(p, comma, ps)
                }
            and functionType size = gen {
                let! funToken = reserved
                let! l = reserved
                let! m1 = Gen.optionOf (parameters1 (size / 2))
                let! r = reserved
                let! colon = reserved
                let! m2 = typeSignOrWrap D.Precedence.FunctionType (size / 2)
                return D.FunctionType(funToken, l, m1, r, colon, m2)
                }

            Gen.sized typeSignNoWrap'

        let rec validTypeSign minPrecedence t =
            minPrecedence <= DocumentPrinter.typePrecedence t &&
            match t with
            | D.EmptyType _
            | D.NilType _ -> true
            | D.ArrayType(e, _, _) -> validTypeSign D.Precedence.ArrayType e.kind
            | D.ConstrainedType(t, _, fs) ->
                validTypeSign D.Precedence.PrimitiveType t.kind &&
                validFields fs

            | D.FunctionType(_, _, ps, _, _, rt) ->
                Option.forall validParameters ps &&
                validTypeSign D.Precedence.FunctionType rt.kind

            | D.InterfaceType fs -> validFields fs
            | D.MultiType2(p, _, ps) -> validParameter p && validParameters ps
            | D.NamedType(_, ts) -> Option.forall validGenericArguments ts
            | D.SingleMultiType(_, p, _, _) -> validParameter p
            | D.VariadicType { kind = D.VariadicTypeSign(_, _, et) } ->
                Option.forall (fun t -> validTypeSign D.Precedence.ConstrainedType t.kind) et

            | D.WrappedType(_, t, _) -> validTypeSign D.Precedence.PrimitiveType t.kind

        and validFields { kind = D.Fields(_, fs, _, _) } =
            fs
            |> SepBy.toList
            |> Seq.forall validField

        and validField { kind = D.Field(_, _, t) } =
            validTypeSign D.Precedence.ConstrainedType t.kind

        and validParameters (D.Parameters ps) =
            ps
            |> SepBy.toList
            |> Seq.forall validParameter

        and validParameter { kind = D.Parameter(_, t) } =
            validTypeSign D.Precedence.ConstrainedType t.kind

        and validGenericArguments (D.GenericArguments(_, ts, _, _)) =
            ts
            |> SepBy.toList
            |> Seq.forall (fun x -> validTypeSign D.Precedence.ConstrainedType x.kind)

        let shrink = Arb.Default.Derive<'A D.TypeSign'>().Shrinker
        let shrink x = seq {
            for x in shrink x do
                if validTypeSign D.Precedence.Type x then
                    x
        }
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
