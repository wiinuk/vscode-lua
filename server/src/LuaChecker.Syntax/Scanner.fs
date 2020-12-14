module LuaChecker.Scanner
open Cysharp.Text
open LuaChecker.Primitives
open LuaChecker.Syntax
open LuaChecker.Syntaxes
open System
open System.Diagnostics
open System.Globalization
open System.Text


[<Struct>]
type TokenStructure = {
    mutable hasValue: bool
    mutable _kind: TokenKind
    mutable _leadingTriviaLength: int
    mutable _span: Span
    mutable _trailingTriviaLength: int
}
[<DebuggerDisplay("{_DebugDisplay,nq}")>]
type Scanner<'Error> = {
    mutable _source: string
    mutable first: int
    mutable last: int
    mutable skipTrivia: bool

    mutable position: int
    mutable currentTokenStructure: TokenStructure
    mutable remainingTriviaLength: int
    mutable errors: 'Error list
}
with
    [<DebuggerBrowsable(DebuggerBrowsableState.Never)>]
    member private s._DebugDisplay =
        let { _source = source; first = first; last = last; position = position } = s

        if last - first <= 0 then "┃┃" else
        if position < first then "▶┃" + source.[first..last-1] + "┃" else
        if last = position then "┃" + source.[first..last-1] + "▶┃" else
        if last < position then "┃" + source.[first..last-1] + "┃▶" else
        "┃" + source.[first..position-1] + "▶" + source.[position..last-1] + "┃"

[<Struct>]
type ScannerState<'Error> = {
    _position: int
    _currentTokenStructure: TokenStructure
    _remainingTriviaLength: int
    _errors: 'Error list
}

let peek s: _ inref = &s.currentTokenStructure

let tokenKind s =
    if s.currentTokenStructure.hasValue
    then s.currentTokenStructure._kind
    else TokenKind.Unknown

let tokenSpan s =
    if s.currentTokenStructure.hasValue
    then s.currentTokenStructure._span
    else Span.empty

let getState s = {
    _position = s.position
    _currentTokenStructure = s.currentTokenStructure
    _remainingTriviaLength = s.remainingTriviaLength
    _errors = s.errors
}
let setState (state: _ inref) s =
    s.position <- state._position
    s.currentTokenStructure <- state._currentTokenStructure
    s.remainingTriviaLength <- state._remainingTriviaLength
    s.errors <- state._errors

let currentErrors s = s.errors
let addError s e = s.errors <- e::s.errors
let addErrorAtCurrentToken s error =
    let span = tokenSpan s
    let span =
        if Span.isEmpty span then
            let p = s.position
            { start = p; end' = p }
        else
            span

    match s.errors with
    | struct(lastSpan, _)::_ when lastSpan.start = span.start -> ()
    | _ -> addError s struct(span, error)

let isEos s = s.last <= s.position
let ensure length s = s.position + length <= s.last
let unsafeGet i s = s._source.[i]
let position s = s.position
let sourcePosition s = position s
let unsafePeek s = unsafeGet (position s) s
let unsafeSubstring start length s = s._source.Substring(start, length)
let unsafeAdvance s = s.position <- s.position + 1

let unsafeAdvanceN count s = s.position <- s.position + count

let unsafeRead s =
    let c = unsafePeek s
    unsafeAdvance s
    c

let inline readIf predicate s =
    if isEos s then ValueNone else

    let c = unsafePeek s
    if predicate c then
        unsafeAdvance s
        ValueSome c
    else
        ValueNone

let inline readChar target s = readIf (fun c -> c = target) s |> ValueOption.isSome
let inline skipIf predicate s = readIf predicate s |> ValueOption.isSome
let peek1 s =
    if isEos s then ValueNone else
    ValueSome(unsafeGet (position s) s)

let peek2 s =
    if not <| ensure 2 s then ValueNone else

    let p = position s
    ValueSome struct(unsafeGet p s, unsafeGet (p + 1) s)

let readChar2 (c1, c2) s =
    if not <| ensure 2 s then false else
    let p = position s
    if unsafeGet p s = c1 && unsafeGet (p + 1) s = c2 then
        unsafeAdvanceN 2 s
        true
    else
        false

let readChar3 (c1, c2, c3) s =
    if not <| ensure 3 s then false else
    let p = position s
    if unsafeGet p s = c1 && unsafeGet (p + 1) s = c2 && unsafeGet (p + 2) s = c3 then
        unsafeAdvanceN 3 s
        true
    else
        false

let isNameHead = function '_' -> true | c -> Char.IsLetter c
let isNameTail c = isNameHead c || ('0' <= c && c <= '9')

let rec skipNameTail s =
    if skipIf isNameTail s then
        skipNameTail s

let rec peekString x i start s =
    if i = String.length x then true else
    if x.[i] <> unsafeGet (start + i) s then false else
    peekString x (i + 1) start s

/// ```regexp
/// [\p{L}_][\p{L}0-9_]*
/// ```
let nameOrKeyword s =
    let start = position s
    if not <| skipIf isNameHead s then TokenKind.Unknown else
    skipNameTail s
    let end' = position s
    let length = end' - start
    match length with
    | 2 ->
        match unsafeGet start s, unsafeGet (start + 1) s with
        | 'd', 'o' -> TokenKind.Do
        | 'i', 'f' -> TokenKind.If
        | 'i', 'n' -> TokenKind.In
        | 'o', 'r' -> TokenKind.Or
        | _ -> TokenKind.Name(unsafeSubstring start length s)
    | 3 ->
        match unsafeGet start s, unsafeGet (start + 1) s, unsafeGet (start + 2) s with
        | 'a', 'n', 'd' -> TokenKind.And
        | 'e', 'n', 'd' -> TokenKind.End
        | 'f', 'o', 'r' -> TokenKind.For
        | 'n', 'i', 'l' -> TokenKind.Nil
        | 'n', 'o', 't' -> TokenKind.Not
        | _ -> TokenKind.Name(unsafeSubstring start length s)
    | 4 ->
        match unsafeGet start s, unsafeGet (start + 1) s, unsafeGet (start + 2) s, unsafeGet (start + 3) s with
        | 't', 'r', 'u', 'e' -> TokenKind.True
        | 'e', 'l', 's', 'e' -> TokenKind.Else
        | 't', 'h', 'e', 'n' -> TokenKind.Then
        | _ -> TokenKind.Name(unsafeSubstring start length s)
    | 5 ->
        match unsafeGet start s, unsafeGet (start + 1) s, unsafeGet (start + 2) s, unsafeGet (start + 3) s, unsafeGet (start + 4) s with
        | 'b', 'r', 'e', 'a', 'k' -> TokenKind.Break
        | 'f', 'a', 'l', 's', 'e' -> TokenKind.False
        | 'l', 'o', 'c', 'a', 'l' -> TokenKind.Local
        | 'u', 'n', 't', 'i', 'l' -> TokenKind.Until
        | 'w', 'h', 'i', 'l', 'e' -> TokenKind.While
        | _ -> TokenKind.Name(unsafeSubstring start length s)
    | 6 ->
        match unsafeGet start s, unsafeGet (start + 1) s, unsafeGet (start + 2) s, unsafeGet (start + 3) s, unsafeGet (start + 4) s, unsafeGet (start + 5) s with
        | 'e', 'l', 's', 'e', 'i', 'f' -> TokenKind.ElseIf
        | 'r', 'e', 'p', 'e', 'a', 't' -> TokenKind.Repeat
        | 'r', 'e', 't', 'u', 'r', 'n' -> TokenKind.Return
        | _ -> TokenKind.Name(unsafeSubstring start length s)
    | 8 ->
        if peekString "function" 0 start s then TokenKind.Function
        else TokenKind.Name(unsafeSubstring start length s)

    | _ ->
        TokenKind.Name(unsafeSubstring start length s)

let isDigit c = '0' <= c && c <= '9'
let isHex c = isDigit c || ('a' <= c && c <= 'f') || ('A' <= c && c <= 'F')
let digitToInt c = int c - int '0'
let digitsMax2 n s =
    match readIf isDigit s with
    | ValueNone -> n
    | ValueSome c ->

    let n = n * 10 + digitToInt c

    match readIf isDigit s with
    | ValueNone -> n
    | ValueSome c ->

    n * 10 + digitToInt c

/// ```regexp
/// [a b f n r t \\ " ' \r \n] | [0-9]{1,3}
/// ```
let escapeTail s =
    if isEos s then ValueNone else
    match unsafeRead s with
    | 'a' -> ValueSome '\a'
    | 'b' -> ValueSome '\b'
    | 'f' -> ValueSome '\f'
    | 'n' -> ValueSome '\n'
    | 'r' -> ValueSome '\r'
    | 't' -> ValueSome '\t'
    | '\\'
    | '"'
    | '\''
    | '\r'
    | '\n' as c -> ValueSome c
    | c when isDigit c -> digitsMax2 (digitToInt c) s |> char |> ValueSome
    | _ -> ValueNone

let rec simpleStringTail (b: Utf16ValueStringBuilder byref) q s =
    if isEos s then false else
    let c = unsafeRead s

    if c = q then true
    elif c = '\\' then
        match escapeTail s with
        | ValueNone -> false
        | ValueSome c -> b.Append c; simpleStringTail &b q s
    else
        b.Append c; simpleStringTail &b q s

/// ```regexp
/// (?<no-esc> [^\\\k<quote>] )
/// (?<esc> \\ ( [a b f n r t \\ " ' \r \n] | [0-9]{1,3} ) )
/// (?<char> \k<no-esc> | \k<esc> )
/// (?<simple> (?<quote> ['"]) \k<char>* \k<quote> )
/// ```
let simpleString s =
    let start = position s
    match readIf (function '\'' | '"' -> true | _ -> false) s with
    | ValueNone -> TokenKind.Unknown
    | ValueSome q ->
        use mutable b = ZString.CreateStringBuilder()
        if simpleStringTail &b q s then TokenKind.String(b.ToString()) else

        s.position <- start
        TokenKind.Unknown

let rec longStringQuoteTail count s =
    if isEos s then ValueNone else
    match unsafePeek s with
    | '=' -> unsafeAdvance s; longStringQuoteTail (count + 1) s
    | '[' -> unsafeAdvance s; ValueSome count
    | _ -> ValueNone

let longStringQuote s =
    if not <| readChar '[' s then ValueNone else
    longStringQuoteTail 0 s

let rec unsafePeekLongStringEndTail count p s =
    match unsafeGet p s with
    | ']' when 0 = count -> true
    | '=' when 0 < count -> unsafePeekLongStringEndTail (count - 1) (p + 1) s
    | _ -> false

let rec longStringTail count s =
    if isEos s then false else

    match unsafeRead s with
    | ']' when ensure (count + 1) s && unsafePeekLongStringEndTail count (position s) s -> unsafeAdvanceN (count + 1) s; true
    | _ -> longStringTail count s

/// ```regexp
/// (?<long> \[(?<eqs>=*)\[ (\r?\n)? ((?! \]\k<eqs>\]).)* \]\k<eqs>\] )
/// ```
let longStringRange s =
    match longStringQuote s with
    | ValueNone -> ValueNone
    | ValueSome count ->

    match peek2 s with
    | ValueSome('\r', '\n') -> unsafeAdvanceN 2 s
    | ValueSome('\n', _) -> unsafeAdvance s
    | _ -> ()

    let start = position s
    if not <| longStringTail count s then ValueNone else

    let length = position s - start - (count + 2)
    ValueSome struct(start, length)

let longString s =
    let start = position s
    match longStringRange s with
    | ValueNone ->
        s.position <- start
        TokenKind.Unknown

    | ValueSome(start, length) ->
        TokenKind.String(unsafeSubstring start length s)

let rec digits0 s = if skipIf isDigit s then digits0 s
let digits1 s = if skipIf isDigit s then digits0 s; true else false

let rec hexes0 s = if skipIf isHex s then hexes0 s
let hexes1 s = if skipIf isHex s then hexes0 s; true else false

let fraction s = if readChar '.' s then digits1 s else true
let exponent s =
    if skipIf (function 'e' | 'E' -> true | _ -> false) s then
        skipIf (function '+' | '-' -> true | _ -> false) |> ignore
        digits1 s
    else
        true

let hexInteger s =
    let start = position s
    if hexes1 s then
        let count = position s - start
        // TODO: UInt32.MaxValue ( 4294967295 ) に切りつめる
        let x = double(bigint.Parse(unsafeSubstring start count s, NumberStyles.HexNumber, null))
        TokenKind.Number x
    else
        TokenKind.Unknown

let number s =
    let start = position s

    if ensure 2 s && unsafeGet start s = '0' && (unsafeGet (start + 1) s = 'x' || unsafeGet (start + 1) s = 'X') then
        unsafeAdvanceN 2 s
        hexInteger s
    else

    if not <| digits1 s || not <| fraction s || not <| exponent s then
        s.position <- start
        TokenKind.Unknown
    else

    let count = position s - start

    let x = double (unsafeSubstring start count s)
    TokenKind.Number x

let rec skipCommentTail s = if skipIf (fun c -> c <> '\n') s then skipCommentTail s

let comment s =
    if readChar2 ('-', '-') s then
        match longStringRange s with
        | ValueSome _ -> ()
        | _ -> skipCommentTail s
        true
    else
        false

let rec trivias0 s = if skipIf Char.IsWhiteSpace s || comment s then trivias0 s

let peekToken3 s =
    let p = position s
    if ensure 3 s && unsafeGet p s = '.' && unsafeGet (p + 1) s = '.' && unsafeGet (p + 2) s = '.' then TokenKind.Dot3 else TokenKind.Unknown

let peekToken2 s =
    let p = position s
    if ensure 2 s then
        match unsafeGet p s, unsafeGet (p + 1) s with
        | '=', '=' -> TokenKind.Eq
        | '~', '=' -> TokenKind.Ne
        | '<', '=' -> TokenKind.Le
        | '>', '=' -> TokenKind.Ge
        | '.', '.' -> TokenKind.Con
        | _ -> TokenKind.Unknown
    else
        TokenKind.Unknown

let peekToken1 s =
    match unsafePeek s with
    | '+' -> TokenKind.Add
    | '*' -> TokenKind.Mul
    | '/' -> TokenKind.Div
    | '%' -> TokenKind.Mod
    | '^' -> TokenKind.Pow
    | '#' -> TokenKind.Len
    | '<' -> TokenKind.Lt
    | '>' -> TokenKind.Gt
    | '=' -> TokenKind.Assign
    | '(' -> TokenKind.LBracket
    | ')' -> TokenKind.RBracket
    | '{' -> TokenKind.LCBracket
    | '}' -> TokenKind.RCBracket
    | '[' -> TokenKind.LSBracket
    | ']' -> TokenKind.RSBracket
    | ';' -> TokenKind.Semicolon
    | ':' -> TokenKind.Colon
    | ',' -> TokenKind.Comma
    | '.' -> TokenKind.Dot
    | '-' -> TokenKind.Sub
    | '@' -> TokenKind.At
    | _ -> TokenKind.Unknown

let readTokenKind s =
    let k = peekToken3 s
    if k <> TokenKind.Unknown then unsafeAdvanceN 3 s; k else

    match peek2 s with
    | ValueSome(('[', '[') | ('[', '=')) -> longString s
    | _ ->

    let k = peekToken2 s
    if k <> TokenKind.Unknown then unsafeAdvanceN 2 s; k else

    if isEos s then TokenKind.Unknown else

    let k = peekToken1 s
    if k <> TokenKind.Unknown then unsafeAdvanceN 1 s; k else

    match unsafePeek s with
    | '"'
    | '\'' -> simpleString s
    | c1 when '0' <= c1 && c1 <= '9' -> number s
    | _ -> nameOrKeyword s

let skipTrivias s =
    if s.skipTrivia then
        let start = position s
        trivias0 s
        position s - start
    else
        0

let leadingTriviaAndToken s =
    let leadingTriviaLength = skipTrivias s
    let start = sourcePosition s
    match readTokenKind s with
    | TokenKind.Unknown -> ValueNone
    | k ->
    let end' = sourcePosition s

    let trivia = {
        leadingTriviaLength = leadingTriviaLength
        leadingDocument = None
        span = {
            start = start
            end' = end'
        }
        trailingTriviaLength = 0
        trailingDocument = None
    }
    ValueSome {
        kind = k
        trivia = trivia
    }

let takeTrivia s =
    if s.currentTokenStructure.hasValue then
        let s = &s.currentTokenStructure
        let l = s._leadingTriviaLength
        s._leadingTriviaLength <- 0
        struct(l, s._span.start)
    else
        struct(s.remainingTriviaLength, s.position)

let readAndSetCurrentToken s =
    let start = sourcePosition s
    match readTokenKind s with
    | TokenKind.Unknown ->
        s.currentTokenStructure.hasValue <- false
        s.currentTokenStructure._kind <- TokenKind.Unknown

    | k ->
    let end' = sourcePosition s

    let leadingTriviaLength = s.remainingTriviaLength
    let trailingTriviaLength = skipTrivias s
    let trailingTriviaLength =
        if isEos s then
            s.remainingTriviaLength <- 0
            trailingTriviaLength
        else
            s.remainingTriviaLength <- trailingTriviaLength
            0

    let s = &s.currentTokenStructure
    s.hasValue <- true
    s._kind <- k
    s._leadingTriviaLength <- leadingTriviaLength
    s._span <- { start = start; end' = end' }
    s._trailingTriviaLength <- trailingTriviaLength

let validateRange source position length =
    if position < 0 || String.length source < position then raise <| IndexOutOfRangeException()
    if length < 0 || String.length source < position + length then raise <| IndexOutOfRangeException()

[<Struct>]
type ScannerCreateOptions = {
    initialRead: bool
    skipTrivia: bool
    position: int
    length: int
}
module ScannerCreateOptions =
    let defaultOptions source = {
        initialRead = true
        skipTrivia = true
        position = 0
        length = String.length source
    }

let private createUninitialized() = {
    _source = null
    first = 0
    last = 0
    skipTrivia = false

    position = 0
    remainingTriviaLength = 0
    currentTokenStructure = Unchecked.defaultof<_>

    errors = Unchecked.defaultof<_>
}
let initCore (options: _ inref) source s =
    let { position = position; length = length } = options
    validateRange source position length

    s._source <- source
    s.first <- position
    s.last <- position + length
    s.skipTrivia <- options.skipTrivia

    s.position <- position
    s.remainingTriviaLength <- 0
    s.currentTokenStructure <- Unchecked.defaultof<_>
    s.currentTokenStructure._kind <- TokenKind.Unknown

    s.errors <- []

    if options.initialRead then
        s.remainingTriviaLength <- skipTrivias s
        readAndSetCurrentToken s

let createCore (options: _ inref) source =
    let s = createUninitialized()
    initCore &options source s
    s

let inline createWith withOptions source =
    let options = withOptions (ScannerCreateOptions.defaultOptions source)
    createCore &options source

let inline initWith withOptions source s =
    let options = withOptions (ScannerCreateOptions.defaultOptions source)
    initCore &options source s

let init source s = initWith (fun x -> x) source s
let create source = createWith (fun x -> x) source

let peekTrivia s =
    let t = &s.currentTokenStructure
    if t.hasValue then
        ValueSome {
            leadingTriviaLength = t._leadingTriviaLength
            leadingDocument = None
            span = t._span
            trailingTriviaLength = t._trailingTriviaLength
            trailingDocument = None
        }
    else
        ValueNone

let unsafeReadTrivia s =
    let t = &s.currentTokenStructure
    let t = {
        leadingTriviaLength = t._leadingTriviaLength
        leadingDocument = None
        span = t._span
        trailingTriviaLength = t._trailingTriviaLength
        trailingDocument = None
    }
    readAndSetCurrentToken s
    t

let unsafeReadSpan s =
    let t = &s.currentTokenStructure._span
    readAndSetCurrentToken s
    t

let read s =
    if s.currentTokenStructure.hasValue
    then ValueSome { kind = s.currentTokenStructure._kind; trivia = unsafeReadTrivia s }
    else ValueNone

let readSpan s =
    if s.currentTokenStructure.hasValue
    then ValueSome <| unsafeReadSpan s
    else ValueNone

let skip s =
    if s.currentTokenStructure.hasValue then
        readAndSetCurrentToken s

let inline readPick chooser s =
    match chooser (tokenKind s) with
    | ValueSome x -> ValueSome struct(x, unsafeReadTrivia s)
    | _ -> ValueNone

let readToken kind s =
    if tokenKind s = kind then unsafeReadTrivia s |> ValueSome
    else ValueNone

let readTokenSpan kind s =
    if tokenKind s = kind
    then readSpan s
    else ValueNone

[<AbstractClass; Sealed>]
type private PoolHolder<'Error> private () =
    static let value: 'Error Scanner Pool = Pool.create 128 (fun _ -> createUninitialized()) (init "")
    static member Value = value

let pool<'Error> = PoolHolder<'Error>.Value
