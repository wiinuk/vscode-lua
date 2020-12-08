module LuaChecker.Scanner.Tests
open FsCheck
open LuaChecker
open LuaChecker.Syntax
open LuaChecker.Syntax.Printer
open LuaChecker.Syntaxes
open LuaChecker.Checker.Test.Utils
open System
open Xunit


let tokenizeRange source position length =
    let s = Scanner.createWith (fun c -> { c with position = position; length = length }) source
    let rec aux acc =
        match Scanner.read s with
        | ValueNone -> List.rev acc
        | ValueSome t -> aux (t::acc)
    aux []

let tokenize source = tokenizeRange source 0 source.Length

let private span sp (sl, sc) ep (el, ec) = {
    start = sp
    end' = ep
}

type private K = TokenKind

type CommentOrWhiteSpace =
    | LineComment of string NonNull
    | LongComment of string NonNull
    | WhiteSpace
    | NewLine

type TokenPrintConfig = {
    leadingTrivias: (CommentOrWhiteSpace * PositiveInt) list
    trailingTrivias: (CommentOrWhiteSpace * PositiveInt) list
    config: PrintConfig
}

module TokenPrintConfig =
    let Default = {
        leadingTrivias = []
        trailingTrivias = []
        config = PrintConfig.defaultConfig
    }

let showTrivias trivias = seq {
    for t, PositiveInt eq in trivias do
        match t with
        | WhiteSpace -> " "
        | NewLine -> "\n"
        | LineComment(NonNull x) -> "--"; x.Replace('\n', '⏎'); "\n"
        | LongComment(NonNull x) ->
            let eq = Printer.safeEqCount x eq
            "--["; yield! Printer.eqs eq; "["; x; "]"; yield! Printer.eqs eq; "]"
}
let showTokens tokenKinds = seq {
    for k, config in tokenKinds do
        " "
        yield! showTrivias config.leadingTrivias
        yield! Printer.showKind config.config k
        match k, config.trailingTrivias with
        | K.Sub, (LineComment _, _)::_ -> " "
        | _ -> ()
        yield! showTrivias config.trailingTrivias
}

let roundTripWithNoiseTest tokenKinds (NonNull leadingNoise) (NonNull trailingNoise) =
    let source' = showTokens tokenKinds |> String.concat ""
    let source = leadingNoise + source' + trailingNoise
    let actual = tokenizeRange source leadingNoise.Length source'.Length |> List.map (fun x -> x.kind)
    let expected = tokenKinds |> List.map fst

    let tokenKinds =
        tokenKinds
        |> List.map (fun (k, c) ->
            let k =
                match k with
                | K.String x when not <| isNull x ->
                    x
                    |> String.collect (function
                        | '\\' -> "\\\\"
                        | '"' -> "\\\""
                        | c when Char.IsControl c -> sprintf "\\u%04X" <| int c
                        | c -> string c
                    )
                    |> sprintf "String(\"%s\")"

                | _ -> sprintf "%A" k
            k, c
        )
    Assert.True((actual = expected), sprintf "%A =? %A\ntokens: %A\nsource: %A" actual expected tokenKinds source)

let roundTripPropertyTest ks = roundTripWithNoiseTest ks (NonNull "") (NonNull "")

[<Fact>]
let emptySource() =
    let s = Scanner.create ""
    s.currentTokenStructure.hasValue =? false
    Scanner.read s =? ValueNone
    Scanner.read s =? ValueNone

[<Fact>]
let tokens() =
    let s = Scanner.create " t1  t2   t3    "
    Scanner.read s =? ValueSome {
        kind = TokenKind.Name "t1"
        trivia = {
            leadingTriviaLength = 1
            span = { start = 1; end' = 3 }
            trailingTriviaLength = 0
            leadingDocument = None
            trailingDocument = None
        }
    }
    Scanner.read s =? ValueSome {
        kind = TokenKind.Name "t2"
        trivia = {
            leadingTriviaLength = 2
            span = { start = 5; end' = 7 }
            trailingTriviaLength = 0
            leadingDocument = None
            trailingDocument = None
        }
    }
    Scanner.read s =? ValueSome {
        kind = TokenKind.Name "t3"
        trivia = {
            leadingTriviaLength = 3
            span = { start = 10; end' = 12 }
            trailingTriviaLength = 4
            leadingDocument = None
            trailingDocument = None
        }
    }
    Scanner.read s =? ValueNone
    Scanner.read s =? ValueNone

[<Fact>]
let if'() =
    tokenize "if" =? [
        {
            kind = K.If
            trivia = {
                leadingTriviaLength = 0
                span = span 0 (1, 1) 2 (1, 3)
                trailingTriviaLength = 0
                leadingDocument = None
                trailingDocument = None
            }
        }
    ]

[<Fact>]
let dot() =
    tokenize "." =? [
        {
            kind = K.Dot
            trivia = {
                leadingTriviaLength = 0
                span = span 0 (1, 1) 1 (1, 2)
                trailingTriviaLength = 0
                leadingDocument = None
                trailingDocument = None
            }
        }
    ]

[<Fact>]
let ifWithComment() =
    tokenize "if-- comment" =? [
        {
            kind = K.If
            trivia = {
                leadingTriviaLength = 0
                span = span 0 (1, 1) 2 (1, 3)
                trailingTriviaLength = 10
                leadingDocument = None
                trailingDocument = None
            }
        }
    ]

[<Fact>]
let trivias() =
    tokenize "--[[a]]break -- b\n --[[c]] function -- d" =? [
        {
            kind = K.Break
            trivia = {
                leadingTriviaLength = 7
                span = span 7 (1, 8) 12 (1, 13)
                trailingTriviaLength = 0
                leadingDocument = None
                trailingDocument = None
            }
        }
        {
            kind = K.Function
            trivia = {
                leadingTriviaLength = 15
                span = span 27 (2, 10) 35 (2, 18)
                trailingTriviaLength = 5
                leadingDocument = None
                trailingDocument = None
            }
        }
    ]

[<Fact>]
let singleCommentProperty() = check <| fun (PositiveInt eqCount) ->
    let s = String('=', eqCount) |> sprintf "0--[%s\n1" |> Scanner.create

    Scanner.read s =? ValueSome {
        kind = TokenKind.Number 0.
        trivia = {
            leadingTriviaLength = 0
            span = { start = 0; end' = 1 }
            trailingTriviaLength = 0
            leadingDocument = None
            trailingDocument = None
        }
    }
    Scanner.read s =? ValueSome {
        kind = TokenKind.Number 1.
        trivia = {
            leadingTriviaLength = 4 + eqCount
            span = { start = 5 + eqCount; end' = 6 + eqCount }
            trailingTriviaLength = 0
            leadingDocument = None
            trailingDocument = None
        }
    }
    Scanner.read s =? ValueNone

let longStringConfig = { TokenPrintConfig.Default with config = { TokenPrintConfig.Default.config with stringStyle = LongString } }

[<Fact>]
let longStringRoundTrip() =
    roundTripPropertyTest [
        K.String "\r\n", longStringConfig
    ]
    roundTripPropertyTest [
        K.String "\n", longStringConfig
    ]
    roundTripPropertyTest [
        K.String "\r", longStringConfig
    ]
    roundTripPropertyTest [
        K.String "", longStringConfig
    ]
    roundTripPropertyTest [
        K.String "]", longStringConfig
    ]

[<Fact>]
let controlEscapeRoundTrip() =
    roundTripPropertyTest [
        K.String "\0228", { TokenPrintConfig.Default with config = { TokenPrintConfig.Default.config with charEscape = Control } }
    ]

[<Fact>]
let trueRoundTrip() =
    roundTripPropertyTest [
        K.True, TokenPrintConfig.Default
    ]

[<Fact>]
let mulRoundTrip() =
    roundTripPropertyTest [
        K.Mul, TokenPrintConfig.Default
    ]

[<Fact>]
let tokensRoundTrip() = check roundTripWithNoiseTest

[<Fact>]
let subAndLineCommentRoundTrip() =
    roundTripWithNoiseTest
        [
            TokenKind.Sub,
            { TokenPrintConfig.Default with
                trailingTrivias =
                [
                    LineComment (NonNull ""), PositiveInt 1
                ]
            }
        ]
        (NonNull "") (NonNull "")

[<Fact>]
let lineMap() =
    let pos = Position

    let ls = LineMap.create ""
    LineMap.findPosition -1 ls =? pos(0, -1)
    LineMap.findPosition 0 ls =? pos(0, 0)
    LineMap.findPosition 1 ls =? pos(0, 1)

    let ls = LineMap.create "0\n23\n567"
    LineMap.findPosition -1 ls =? pos(0, -1)
    LineMap.findPosition 0 ls =? pos(0, 0)
    LineMap.findPosition 1 ls =? pos(0, 1)
    LineMap.findPosition 2 ls =? pos(1, 0)
    LineMap.findPosition 3 ls =? pos(1, 1)
    LineMap.findPosition 4 ls =? pos(1, 2)
    LineMap.findPosition 5 ls =? pos(2, 0)
    LineMap.findPosition 6 ls =? pos(2, 1)
    LineMap.findPosition 7 ls =? pos(2, 2)
    LineMap.findPosition 8 ls =? pos(2, 3)

[<Fact>]
let createUnread() =
    let s = Scanner.createWith (fun c -> { c with initialRead = false }) "---@a"
    s.currentTokenStructure.hasValue =? false

[<Fact>]
let incompleteLongComment() =
    let s = Scanner.createWith (fun c -> { c with initialRead = false }) "--[["
    Scanner.read s =? ValueNone
    s.position =? 0

[<Fact>]
let incompleteNumber() =
    let s = Scanner.createWith (fun c -> { c with initialRead = false }) "0x"
    Scanner.read s =? ValueNone
    s.position =? 0

[<Fact>]
let incompleteString() =
    let s = Scanner.createWith (fun c -> { c with initialRead = false }) "'abc"
    Scanner.read s =? ValueNone
    s.position =? 0

[<Fact>]
let implicitSkipTrivias() =
    let s = Scanner.createWith (fun c -> { c with skipTrivia = false }) "a b"
    Scanner.tokenKind s =? K.Name "a"
    Scanner.trivias0 s
    Scanner.skip s
    Scanner.tokenKind s =? K.Name "b"
