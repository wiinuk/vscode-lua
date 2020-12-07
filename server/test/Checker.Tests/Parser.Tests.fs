module LuaChecker.Parser.Tests
open LuaChecker
open LuaChecker.Syntax.Printer
open LuaChecker.Syntaxes
open LuaChecker.Syntax
open LuaChecker.Checker.Test.Utils
open LuaChecker.Primitives
open LuaChecker.Parser
open Xunit


type K = Syntax.TokenKind
let token kind = {
    kind = kind
    trivia = Trivia.createEmpty()
}
let name = token >> Name
let keyword =  token HEmpty
let emptySource x = { kind = x; trivia = Span.empty }

let triviaT ltl (start, end') ttl = {
    leadingTriviaLength = ltl
    leadingDocument = None
    span = { start = start; end' = end' }
    trailingTriviaLength = ttl
    trailingDocument = None
}
let keywordT ltl (start, end') ttl = {
    kind = HEmpty
    trivia = triviaT ltl (start, end') ttl
}

module Var =
    let id n = name n |> Variable |> emptySource

module SepBy =
    let tryOfList sep = function
        | [] -> None
        | x::xs -> Some <| SepBy(x, List.map (fun x -> sep, x) xs)

    let ofList sep xs =
        tryOfList sep xs
        |> Option.defaultWith (fun _ -> failwithf "empty list")

module Field =
    let sep = token Comma
    let init x = Init x |> emptySource

module Exp =
    let ofVar x = Var x |> emptySource |> PrefixExp |> emptySource
    let toPrefixExp x =
        match x.kind with
        | PrefixExp f -> f
        | f -> Wrap(keyword, emptySource f, keyword) |> emptySource

    let callExps f args =
        let args = SepBy.tryOfList keyword args |> Option.map emptySource
        let args = Args(keyword, args, keyword) |> emptySource
        Call(toPrefixExp f, args) |> emptySource

    let id n = Variable(name n) |> emptySource |> ofVar
    let member' e n = Member(toPrefixExp e, keyword, name n) |> emptySource |> ofVar
    let wrap e = Wrap(keyword, e, keyword) |> emptySource |> PrefixExp |> emptySource
    let call f args = Apply(callExps f args) |> emptySource |> PrefixExp |> emptySource
    let varArg = VarArg keyword |> emptySource
    let literal x = Literal(token x) |> emptySource
    let binary x1 x2 x3 = Binary(x1, token x2, x3) |> emptySource
    let newTable xs =
        let xs = SepBy.ofList Field.sep xs
        let x = TableConstructor(keyword, Some(FieldList(xs, None)), keyword) |> emptySource
        NewTable x |> emptySource

module Stat =
    let assign vars values =
        let vars = SepBy.ofList keyword vars |> emptySource
        let values = SepBy.ofList keyword values |> emptySource
        Assign(vars, keyword, values) |> emptySource

    let call f args = Exp.callExps f args |> FunctionCall |> emptySource
    let for' var start end' (stats, lastStat) =
        let stats = List.map (fun x -> x, None) stats
        let lastStat = Option.map (fun x -> x, None) lastStat
        For(keyword, Name(token var), keyword, start, keyword, end', None, keyword, { stats = stats; lastStat = lastStat } |> token, keyword)
        |> emptySource

let toEmptyTrivia _ = Trivia.createEmpty()
let toEmptySpan _ = Span.empty

let parse p map source =
    let s = Scanner.create source
    match p s with
    | Ok x -> Ok((map (toEmptySpan, toEmptyTrivia) x).kind, source.[s.position..])
    | Error e -> Error e

let roundTripTest printer parser map config expected =
    let env = { config = config; printToken = printToken }
    printer env expected
    |> String.concat ""
    |> parse parser map =? Ok((map (toEmptySpan, toEmptyTrivia) expected).kind, "")

let roundTripExpTest config = roundTripTest Printer.exp Parser.exp Exp.map config
let roundTripStatTest config = roundTripTest Printer.stat Parser.stat Stat.map config
let roundTripVarTest config = roundTripTest Printer.var Parser.var Var.map config
let roundTripBlockTest config = roundTripTest Printer.block Parser.block Block.map config

[<Fact>]
let nilExp() =
    parse exp Exp.map "nil" =? Ok(Literal(token Nil), "")

[<Fact>]
let doStat() =
    parse stat Stat.map "do end"
    =? Ok(Do(keyword, token { stats = []; lastStat = None }, keyword), "")

[<Fact>]
let callStat() =
    "a = f\n(g).x(a)"
    |> parse block Block.map
    =? Ok(
        {
            stats = [
                Stat.assign [Var.id "a"] [Exp.id "f"], None
                Stat.call (Exp.member' (Exp.wrap(Exp.id "g")) "x") [Exp.id "a"], None
            ]
            lastStat = None
        }, ""
    )

    "a = f(g).x(a)"
    |> parse block Block.map
    =? Ok(
        {
            stats = [
                Stat.assign [Var.id "a"] [
                    Exp.call (Exp.member' (Exp.call (Exp.id "f") [Exp.id "g"]) "x") [Exp.id "a"]
                ], None
            ]
            lastStat = None
        }, ""
    )

[<Fact>]
let callRoundTrip() =
    // f()
    Stat.call (Exp.id "f") []
    |> roundTripStatTest PrintConfig.defaultConfig

[<Fact>]
let memberRoundTrip() =
    // a.a
    Member(Var(Var.id "a") |> emptySource, keyword, Name(token "a")) |> emptySource
    |> roundTripVarTest PrintConfig.defaultConfig

[<Fact>]
let forRoundTrip() =
    Stat.for' "a" Exp.varArg Exp.varArg ([], None)
    |> roundTripStatTest PrintConfig.defaultConfig

[<Fact>]
let mulRoundTrip() =
    Exp.binary (Exp.literal Nil) Mul (Exp.literal True)
    |> roundTripExpTest PrintConfig.defaultConfig

[<Fact>]
let newTableInitRoundTrip() =
    // `{ a }`
    Exp.newTable [Field.init(Exp.id "a")]
    |> roundTripExpTest PrintConfig.defaultConfig

[<Fact>]
let functionCallRoundTrip() =
    // repeat until a
    // (f)()
    {
        stats = [
            RepeatUntil(
                keyword,
                { stats = []; lastStat = None } |> token,
                keyword,
                PrefixExp(Var(Variable(Name(token "a")) |> emptySource) |> emptySource) |> emptySource
            )
            |> emptySource, None
            FunctionCall(
                Call(
                    Wrap(
                        keyword,
                        PrefixExp(Var(Variable(Name(token "f")) |> emptySource) |> emptySource) |> emptySource,
                        keyword
                    )
                    |> emptySource,
                    Args(keyword, None, keyword)  |> emptySource
                )
                |> emptySource
            )
            |> emptySource, None
        ]
        lastStat = None
    }
    |> token
    |> roundTripBlockTest PrintConfig.defaultConfig

[<Fact>]
let roundTripExpProperty() = check roundTripExpTest
[<Fact>]
let roundTripStatProperty() = check roundTripStatTest
[<Fact>]
let roundTripVarProperty() = check roundTripVarTest
[<Fact>]
let roundTripBlockProperty() = check roundTripBlockTest

[<Fact(DisplayName = "do --[[abc]] end")>]
let emptyBlock() =
    let s = Scanner.create "do --[[abc]] end"
    stat s =? Ok {
        kind =
            Do(
                keywordT 0 (0, 2) 0,
                {
                    kind = { stats = []; lastStat = None }
                    trivia = triviaT 11 (13, 13) 0
                },
                keywordT 0 (13, 16) 0
            )
        trivia = { start = 0; end' = 16 }
    }

[<Fact(DisplayName = "--[[abc]]")>]
let emptyBlockIncludeTrivia() =
    let s = Scanner.create "--[[abc]]"
    block s =? Ok {
        kind = {
            stats = []
            lastStat = None
        }
        trivia = triviaT 9 (9, 9) 0
    }
