module LuaChecker.Parser
open Cysharp.Text
open LuaChecker.Syntaxes
open LuaChecker.Syntax
open LuaChecker.ParserCombinator
open LuaChecker.Primitives
type private K = TokenKind
type private E = Syntax.ParseError

module Errors =
    let tokenKinds = [
        for c in Reflection.FSharpType.GetUnionCases(typeof<TokenKind>) do
            if c.GetFields().Length = 0 then
                Reflection.FSharpValue.MakeUnion(c, null) :?> TokenKind
    ]
    let requireTokenCache =
        tokenKinds
        |> Seq.map (fun k -> k, E.RequireToken k)
        |> Map.ofSeq

    let findRequireToken kind = requireTokenCache.[kind]

    let requireFieldSep = E.RequireFieldSep
module E = Errors

[<AutoOpen>]
module private Helpers =
    let inline withTrivia measure x = { kind = x; trivia = measure x }
    let withSpan2 start end' kind = { kind = kind; trivia = Span.merge start end' }
    let inline toTrivial make measure x = make x |> withTrivia measure
    let inline trivial measure x = mapResult (withTrivia measure) x
    let makeBinary (x1, x2, x3) = Binary(x1, x2, x3) |> withTrivia Exp.measure
    let varToPrefixExp x = withTrivia Var.measure x |> Var |> withTrivia PrefixExp.measure
    let functionCallToPrefixExp x = withTrivia FunctionCall.measure x |> Apply |> withTrivia PrefixExp.measure

    let inline sepBy sep p s = sepBy sep p s |> mapResult (fun struct(x, xs) -> SepBy(x, xs))
    let inline pipe7 (p1, p2, p3, p4, p5, p6, p7) f s =
        pipe5 (p1, p2, p3, p4, pipe3 (p5, p6, p7) id) (fun (x1, x2, x3, x4, (x5, x6, x7)) -> f(x1, x2, x3, x4, x5, x6, x7)) s

    let inline pipe10 (p1, p2, p3, p4, p5, p6, p7, p8, p9, p10) f s =
        pipe5 (p1, p2, p3, p4, pipe5 (p5, p6, p7, p8, pipe2 (p9, p10) id) id) (fun (x1, x2, x3, x4, (x5, x6, x7, x8, (x9, x10))) -> f(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10)) s

    let token kind s =
        match Scanner.readToken kind s with
        | ValueSome t -> Ok { kind = HEmpty; trivia = t }
        | _ -> Error <| Errors.findRequireToken kind

let name s =
    match Scanner.readPick (function K.Name x -> ValueSome x | _ -> ValueNone) s with
    | ValueSome(x, t) -> Ok <| Name { kind = x; trivia = t }
    | _ -> Error E.RequireName

let stringArg s =
    match Scanner.readPick (function K.String x -> ValueSome x | _ -> ValueNone) s with
    | ValueSome(x, t) -> Ok(StringArg(StringLiteral { kind = x; trivia = t }) |> withTrivia Args.measure)
    | _ -> Error E.RequireString

let dot s = token K.Dot s
let dot3 s = token K.Dot3 s
let comma s = token K.Comma s
let assign s = token K.Assign s
let colon s = token K.Colon s
let lBracket s = token K.LBracket s
let rBracket s = token K.RBracket s
let lsBracket s = token K.LSBracket s
let rsBracket s = token K.RSBracket s
let for' s = token K.For s
let do' s = token K.Do s
let end' s = token K.End s
let then' s = token K.Then s
let function' s = token K.Function s
let local s = token K.Local s

let (|LiteralKind|) = function
    | K.Nil -> Nil |> ValueSome
    | K.True -> True |> ValueSome
    | K.False -> False |> ValueSome
    | K.Number x -> Number x |> ValueSome
    | K.String x -> String x |> ValueSome
    | _ -> ValueNone

let (|FieldSepKind|) = function
    | K.Comma -> Comma |> ValueSome
    | K.Semicolon -> Semicolon |> ValueSome
    | _ -> ValueNone

let (|MulOpKind|) = function
    | K.Mul -> Mul |> ValueSome
    | K.Div -> Div |> ValueSome
    | K.Mod -> Mod |> ValueSome
    | _ -> ValueNone

let (|AddOpKind|) = function
    | K.Add -> Add |> ValueSome
    | K.Sub -> Sub |> ValueSome
    | _ -> ValueNone

let (|RelationalOpKind|) = function
    | K.Lt -> Lt |> ValueSome
    | K.Le -> Le |> ValueSome
    | K.Gt -> Gt |> ValueSome
    | K.Ge -> Ge |> ValueSome
    | K.Eq -> Eq |> ValueSome
    | K.Ne -> Ne |> ValueSome
    | _ -> ValueNone

let (|UnaryOpKind|) = function
    | K.Sub -> Neg |> ValueSome
    | K.Not -> Not |> ValueSome
    | K.Len -> Len |> ValueSome
    | _ -> ValueNone

let literal s =
    match Scanner.readPick (function LiteralKind k -> k) s with
    | ValueSome(k, t) -> Ok(Literal { kind = k; trivia = t })
    | _ -> Error E.RequireLiteral

let fieldSep s =
    match Scanner.readPick (function FieldSepKind(ValueSome k) -> ValueSome k | _ -> ValueNone) s with
    | ValueSome(k, t) -> Ok { kind = k; trivia = t }
    | _ -> Error E.requireFieldSep

let unaryOp s =
    match Scanner.readPick (function UnaryOpKind(ValueSome k) -> ValueSome k | _ -> ValueNone) s with
    | ValueSome(k, t) -> Ok { kind = k; trivia = t }
    | _ -> Error E.RequireUnaryOp

let nameList s = sepBy comma name s |> mapResult (withTrivia (Span.sepBy Name.measure))
let funcName s =
    pipe3 (
        name,
        list (tuple2 (dot, name)),
        option (tuple2 (colon, name))
        )
        (FuncName >> withTrivia FuncName.measure)
        s

let namesParameterList s = pipe2 (nameList, option (tuple2 (comma, dot3))) ParameterList s
let varParameterList s = dot3 s |> mapResult VarParameter
let parameterList s =
    match Scanner.tokenKind s with
    | K.Dot3 -> varParameterList s
    | _ -> namesParameterList s
    |> trivial ParameterList.measure

let inline binaryOp (|OpKind|) s =
    match Scanner.readPick (function OpKind x -> x) s with
    | ValueSome(k, t) -> Ok { kind = k; trivia = t }
    | _ -> Error E.RequireBinaryOp

let mulOp s = binaryOp (|MulOpKind|) s
let addOp s = binaryOp (|AddOpKind|) s
let concatOp s = binaryOp (function K.Con -> ValueSome Con | _ -> ValueNone) s
let relationalOp s = binaryOp (|RelationalOpKind|) s
let andOp s = binaryOp (function K.And -> ValueSome And | _ -> ValueNone) s
let orOp s = binaryOp (function K.Or -> ValueSome Or | _ -> ValueNone) s
let powOp s = binaryOp (function K.Pow -> ValueSome Pow | _ -> ValueNone) s
let conOp s = binaryOp (function K.Con -> ValueSome Con | _ -> ValueNone) s

let rec _ = ()

and functionExp s = pipe2 (function', funcBody) Function s
and primExp s =
    match Scanner.tokenKind s with
    | K.Dot3 -> mapResult VarArg (dot3 s)
    | K.Function -> functionExp s
    | K.LCBracket -> mapResult NewTable (tableConstructor s)
    | K.Nil
    | K.True
    | K.False
    | K.Number _
    | K.String _ -> literal s
    | _ -> mapResult PrefixExp (prefixExp s)
    |> trivial Exp.measure

and powExp s = chainR primExp powOp makeBinary s
and unaryExp s = prefixOps (fun (op, x) -> Unary(op, x) |> withTrivia Exp.measure) unaryOp powExp s
and mulExp s = chainL unaryExp mulOp (toTrivial Binary Exp.measure) s
and addExp s = chainL mulExp addOp makeBinary s
and concatExp s = chainR addExp concatOp makeBinary s
and relationalExp s = chainL concatExp relationalOp makeBinary s
and andExp s = chainL relationalExp andOp makeBinary s
and orExp s = chainL andExp orOp makeBinary s
and exp s = orExp s

and expList s = sepBy comma exp s |> mapResult (withTrivia (Span.sepBy Source.measure))

and indexInit s = pipe5 (lsBracket, exp, rsBracket, assign, exp) IndexInit s
and memberInitTail x1 s = pipe2 (assign, exp) (fun (x2, x3) -> MemberInit(x1, x2, x3)) s
and field s =
    match Scanner.tokenKind s with
    | K.Unknown -> Error E.RequireAnyField
    | K.LSBracket -> indexInit s
    | K.Name x ->

        // /\k<name>   =  .*/ => /\k<name> = \k<exp>/
        // /\k<name> [^=] .*/ => /\k<exp>/
        let s' = Scanner.getState s
        let t = Scanner.unsafeReadTrivia s
        match Scanner.tokenKind s with
        | K.Assign -> memberInitTail (Name { kind = x; trivia = t }) s
        | _ ->
            Scanner.setState &s' s
            mapResult Init (exp s)

    | _ -> mapResult Init (exp s)
    |> trivial Field.measure

and fieldList s = pipe2 (sepBy fieldSep field, option fieldSep) FieldList s

and tableConstructor s =
    pipe3
        (token K.LCBracket, option fieldList, token K.RCBracket)
        (toTrivial TableConstructor TableConstructor.measure)
        s

and hasLeadingNewLine s =
    let s' = Scanner.peek s
    if s'._kind = K.Unknown then false else

    let leadingTriviaLength = s'._leadingTriviaLength
    1 <= leadingTriviaLength && 0 <= s._source.IndexOf('\n', s'._span.start - leadingTriviaLength, leadingTriviaLength)

and wrappedArgs s =
    if hasLeadingNewLine s then Error E.DisallowedLeadingNewLine else
    pipe3 (lBracket, option expList, rBracket) (toTrivial Args Args.measure) s

and args s =
    match Scanner.tokenKind s with
    | K.String _ -> stringArg s
    | K.LCBracket -> mapResult (toTrivial TableArg Args.measure) (tableConstructor s)
    | _ -> wrappedArgs s

and varTail x1 s =
    match Scanner.tokenKind s with
    | K.LSBracket -> pipe3 (lsBracket, exp, rsBracket) (fun (x2, x3, x4) -> Index(x1, x2, x3, x4) |> varToPrefixExp) s
    | _ -> pipe2 (dot, name) (fun (x2, x3) -> Member(x1, x2, x3) |> varToPrefixExp) s

and functionCallTail x1 s =
    match Scanner.tokenKind s with
    | K.Colon -> pipe3 (colon, name, args) (fun (x2, x3, x4) -> CallWithSelf(x1, x2, x3, x4) |> functionCallToPrefixExp) s
    | _ -> mapResult (fun x2 -> Call(x1, x2) |> functionCallToPrefixExp) (args s)

and primPrefixExp s =
    match Scanner.tokenKind s with
    | K.LBracket -> pipe3 (lBracket, exp, rBracket) (Wrap >> withTrivia PrefixExp.measure) s
    | _ -> mapResult (Variable >> varToPrefixExp) (name s)

and functionCall s =
    match prefixExp s with
    | Ok { kind = Apply x } -> Ok(FunctionCall x)
    | Ok _ -> Error E.RequireFunctionCall
    | Error e -> Error e

/// `primPrefixExp = name | '(' exp ')'`
/// `callOp = '[' exp ']' | '.' name | args | ':' name args`
/// `prefixExp = primPrefixExp callOp*`
and callOp x s =
    match Scanner.tokenKind s with
    | K.LSBracket
    | K.Dot -> varTail x s
    | _ -> functionCallTail x s

and prefixExp s = postfixOps primPrefixExp callOp s

and var s =
    match prefixExp s with
    | Ok { kind = Var x1 } -> Ok x1
    | Ok _ -> Error E.RequireVar
    | Error e -> Error e

and varList s = sepBy comma var s |> mapResult (withTrivia (Span.sepBy Source.measure))

and funcBody s = pipe5 (lBracket, option parameterList, rBracket, block, token K.End) (FuncBody >> withTrivia FuncBody.measure) s

and returnStat s = pipe2 (token K.Return, option expList) Return s
and lastStat s =
    match Scanner.tokenKind s with
    | K.Return -> returnStat s
    | _ -> mapResult Break (token K.Break s)
    |> trivial LastStat.measure

and elseIfClause s = pipe4 (token K.ElseIf, exp, then', block) (ElseIf >> withTrivia ElseIf.measure) s
and elseClause s = pipe2 (token K.Else, block) (Else >> withTrivia Else.measure) s

and assignStat s = pipe3 (varList, assign, expList) Assign s
and doStat s = pipe3 (do', block, end') Do s
and whileStat s = pipe5 (token K.While, exp, do', block, end') While s
and repeatUntilStat s = pipe4 (token K.Repeat, block, token K.Until, exp) RepeatUntil s
and ifStat s = pipe7 (token K.If, exp, then', block, list elseIfClause, option elseClause, end') If s
and forStat s = pipe10 (for', name, assign, exp, comma, exp, option (tuple2 (comma, exp)), do', block, end') For s
and forInStat s = pipe7 (for', nameList, token K.In, expList, do', block, end') ForIn s
and functionStat s = pipe3 (function', funcName, funcBody) FunctionDecl s
and localFunctionStatTail x1 s = pipe3 (function', name, funcBody) (fun (x2, x3, x4) -> LocalFunction(x1, x2, x3, x4)) s
and localStatTail x1 s = pipe2 (nameList, option (tuple2(assign, expList))) (fun (x2, x3) -> Local(x1, x2, x3)) s
and stat s = stat' s |> trivial Stat.measure
and stat' s =
    match Scanner.tokenKind s with
    | K.Unknown -> Error E.RequireAnyStat
    | K.Do -> doStat s
    | K.While -> whileStat s
    | K.Repeat -> repeatUntilStat s
    | K.If -> ifStat s
    | K.For ->
        let s' = Scanner.getState s
        match forStat s with
        | Ok _ as r -> r
        | _ ->
            Scanner.setState &s' s
            forInStat s

    | K.Function -> functionStat s
    | K.Local ->
        let t = Scanner.unsafeReadTrivia s
        let t = { trivia = t; kind = HEmpty }
        match Scanner.tokenKind s with
        | K.Function -> localFunctionStatTail t s
        | _ -> localStatTail t s
    | _ ->

    let s' = Scanner.getState s
    match assignStat s with
    | Ok _ as r -> r
    | _ ->

    Scanner.setState &s' s
    functionCall s

and blockStats s = list (tuple2 (stat, option (token K.Semicolon))) s
and blockLastStat s = option (tuple2 (lastStat, option (token K.Semicolon))) s
and block s =
    match blockStats s with
    | Error e -> Error e
    | Ok x1 ->

    match blockLastStat s with
    | Error e -> Error e
    | Ok x2 ->

    let b = { stats = x1; lastStat = x2 }
    let trivia =
        match x1, x2 with

        // 空ブロック ( `` や `do end` や `function() end` など )
        // Trivia はブロック自身が持つ
        | [], None ->
            let struct(l, p) = Scanner.takeTrivia s
            { leadingTriviaLength = l; leadingDocument = None; span = { start = p; end' = p }; trailingTriviaLength = 0; trailingDocument = None }

        // 空でなかったので Trivia は葉要素に譲る
        // Block 自身の Trivia は空
        | _ -> { leadingTriviaLength = 0; leadingDocument = None; span = Block.measure b; trailingTriviaLength = 0; trailingDocument = None }

    Ok { kind = b; trivia = trivia }

module private DocumentParserHelpers =
    open System

    let initRange position length ({ Scanner._source = source } as s) =
        Scanner.initWith (fun c -> { c with initialRead = false; skipTrivia = false; position = position; length = length }) source s

    let rec skipWhiteSpaces0 count s = if Scanner.skipIf Char.IsWhiteSpace s then skipWhiteSpaces0 (count + 1) s else count
    let whiteSpaces0 s =
        if 0 < skipWhiteSpaces0 0 s then
            Scanner.readAndSetCurrentToken s
        Ok HEmpty

    let escapeFailureAsRawText (b: Utf16ValueStringBuilder byref) escapeStart s =
        let p' = Scanner.position s
        b.Append(Scanner.unsafeSubstring escapeStart (p' - escapeStart) s)

    /// ;
    let escapeLast (b: _ byref) escapeStart c s =
        if not <| Scanner.readChar ';' s
        then escapeFailureAsRawText &b escapeStart s
        else b.Append(c: char)

    let digits1 s =
        let digitStart = Scanner.position s
        if Scanner.digits1 s then
            let digitEnd = Scanner.position s
            int <| Scanner.unsafeSubstring digitStart (digitEnd - digitStart) s
        else
            -1

    let (|UnescapedName|) =  function
        | "amp" -> ValueSome '&'
        | "quot" -> ValueSome '"'
        | "apos" -> ValueSome '\''
        | "lt" -> ValueSome '<'
        | "gt" -> ValueSome '>'
        | _ -> ValueNone

    /// /(?<escape> &([0-9]+|#[0-9a-fA-F]+|amp|quot|apos|lt|gt); )/
    let escape (b: _ byref) s =
        let escapeStart = Scanner.position s
        if not <| Scanner.readChar '&' s then () else

        match Scanner.peek1 s with
        | ValueNone -> escapeFailureAsRawText &b escapeStart s

        | ValueSome c1 ->

        match c1 with
        | '#' ->
            match Scanner.hexInteger s with
            | K.Number x -> escapeLast &b escapeStart (char (int x)) s
            | _ -> escapeFailureAsRawText &b escapeStart s

        | x when Scanner.isDigit x ->
            let x = char <| digits1 s
            escapeLast &b escapeStart x s

        | _ ->
            match Scanner.nameOrKeyword s with
            | TokenKind.Name(UnescapedName(ValueSome c)) -> escapeLast &b escapeStart c s
            | _ -> escapeFailureAsRawText &b escapeStart s

    /// /(?<comment> [^@\n&] | \k<escape> )/
    let rec skipComments0 (b: Utf16ValueStringBuilder byref) s =
        match Scanner.readIf (function '@' | '\n' | '&' -> false | _ -> true) s with
        | ValueSome c -> b.Append c; skipComments0 &b s
        | _ ->

        match Scanner.peek1 s with
        | ValueSome '&' -> escape &b s; skipComments0 &b s

        | _ -> ()

module DocumentParser =
    open LuaChecker
    open LuaChecker.Syntax.Documents
    open LuaChecker.Syntax
    open System
    open DocumentParserHelpers

    // TODO: Trivia オブジェクトを生成しないようにする
    let tokenSpan k s = token k s |> mapResult (fun x -> x.trivia.span)
    let withTrivia trivia k = { kind = k; trivia = trivia }

    let comments0 (s: _ Scanner.Scanner) =
        if s.currentTokenStructure.hasValue then
            s.position <- s.currentTokenStructure._span.start

        let p0 = Scanner.position s
        let contents =
            use mutable b = ZString.CreateStringBuilder()
            skipComments0 &b s
            b.ToString()
        let p1 = Scanner.position s
        let r = contents |> withTrivia { start = p0; end' = p1 } |> Comment

        s.currentTokenStructure <- Unchecked.defaultof<_>
        s.currentTokenStructure._kind <- K.Unknown
        Scanner.readAndSetCurrentToken s
        Ok r

    let (|FieldKey|) = function
        | K.True -> FieldKey.Bool true |> ValueSome
        | K.False -> FieldKey.Bool false |> ValueSome
        | K.Number x -> FieldKey.Number x |> ValueSome
        | K.String x -> FieldKey.String x |> ValueSome
        | K.Name x -> FieldKey.String x |> ValueSome
        | _ -> ValueNone

    let fieldKey s =
        match Scanner.tokenKind s with
        | K.Sub
        | K.Add as k ->
            let s0 = Scanner.unsafeReadSpan s
            match Scanner.readPick (function K.Number x -> ValueSome x | _ -> ValueNone) s with
            | ValueSome(x, t1) ->
                let sign = if k = K.Sub then -1. else 1.
                FieldKey.Number(x * sign) |> withSpan2 s0 t1.span |> Ok

            | _ ->
                Error E.RequireAnyFieldKey
        | _ ->
            match Scanner.readPick (function FieldKey x -> x) s with
            | ValueSome(k, t) -> k |> withTrivia t.span |> Ok
            | _ -> Error E.RequireAnyFieldKey

    /// name? "..."
    let varParamHead s =
        match Scanner.readTokenSpan K.Dot3 s with
        | ValueSome span -> Ok struct(None, span)
        | _ -> attempt (pipe2 (name, tokenSpan K.Dot3) (fun (Name name as n, d) -> struct(Some n, Span.merge name.trivia.span d))) s

    let makeConstrainedMultiType (struct(n, headSpan), et) =
        let span = Span.merge headSpan et.trivia
        let v = VariadicParameter(n, Some et) |> withTrivia span |> Some
        MultiType([], v) |> withTrivia span

    let rec primitiveType s =
        match Scanner.tokenKind s with
        | K.Name n ->
            let t = Scanner.unsafeReadTrivia s
            let n' = n |> withTrivia t |> Name

            match Scanner.tokenKind s with
            // name "<" …
            | K.Lt -> genericTypeTail n' s
            // "fun" "(" …
            | K.LBracket when n = "fun" -> functionTypeTail n' s
            // name "..." …
            | K.Dot3 -> varParameterTail (Some n') s |> mapResult (fun v -> MultiType([], Some v) |> withTrivia v.trivia)
            // name
            | _ -> namedType n'

        // "{" …
        | K.LCBracket -> interfaceType s
        // "(" …
        | K.LBracket ->
            let s' = Scanner.getState s
            match wrappedType s with
            | Ok _ as r -> r
            | _ ->
                Scanner.setState &s' s
                multiType1 s

        // "..." …
        | K.Dot3 -> varParameterTail None s |> mapResult (fun v -> MultiType([], Some v) |> withTrivia v.trivia)

        | _ -> Error E.RequireAnyTypeSign

    /// name? "..." constrainedType?
    and varParameterTail n s =
        let span = Scanner.unsafeReadSpan s
        let span = Span.merge (Span.option Name.measure n) span

        option constrainedType s
        |> mapResult (fun et ->
            VariadicParameter(n, et)
            |> withSpan2 span (Span.option Source.measure et)
        )

    /// "(" parameter "," ")"
    and multiType1 s =
        pipe4 (tokenSpan K.LBracket, parameter, tokenSpan K.Comma, tokenSpan K.RBracket) (fun (l, p, _, r) ->
            MultiType([p], None) |> withSpan2 l r
        ) s

    and parameter s =
        match Scanner.tokenKind s with
        | K.Name n ->
            let s' = Scanner.getState s
            let nt = Scanner.unsafeReadTrivia s
            let n = n |> withTrivia nt

            match Scanner.tokenKind s with
            // name ":" …
            | K.Colon -> namedParameterTail n s

            // name …
            | _ ->
                Scanner.setState &s' s
                namelessParameter s

        | _ -> namelessParameter s

    and namedType n = NamedType(n, []) |> withTrivia (Name.measure n) |> Ok

    /// "<" functionType ("," functionType)* ">"
    and genericTypeTail n s =
        pipe3 (tokenSpan K.Lt, sepBy (tokenSpan K.Comma) functionType, tokenSpan K.Gt) (fun (_, ts, gt) ->
            NamedType(n, SepBy.toList ts)
            |> withSpan2 (Name.measure n) gt
        ) s

    /// ":" functionType
    and namedParameterTail n s =
        Scanner.skip s
        functionType s
        |> mapResult (fun t ->
            Parameter(Some(Name n), t)
            |> withSpan2 n.trivia.span t.trivia
        )

    /// functionType
    and namelessParameter s =
        functionType s
        |> mapResult (fun t ->
            Parameter(None, t) |> withTrivia t.trivia
        )

    and parameterOrVarParameter s =
        match Scanner.tokenKind s with
        | K.Name n ->
            let s' = Scanner.getState s
            let nt = Scanner.unsafeReadTrivia s
            let n = n |> withTrivia nt

            match Scanner.tokenKind s with
            // name ":" …
            | K.Colon -> namedParameterTail n s |> mapResult Choice1Of2
            // name "..." …
            | K.Dot3 -> varParameterTail (Some(Name n)) s |> mapResult Choice2Of2
            // name …
            | _ ->
                Scanner.setState &s' s
                namelessParameter s |> mapResult Choice1Of2

        // "..." …
        | K.Dot3 -> varParameterTail None s |> mapResult Choice2Of2

        | _ -> namelessParameter s |> mapResult Choice1Of2

    /// ("," parameter)* ("," varParameter)?
    and parameters1Tail acc span s =
        match Scanner.readTokenSpan K.Comma s with
        // ","
        | ValueSome _ ->
            match parameterOrVarParameter s with
            | Error e -> Error e
            // "," varParameter
            | Ok(Choice2Of2 v) -> MultiType(List.rev acc, Some v) |> withSpan2 span v.trivia |> Ok
            // "," parameter …
            | Ok(Choice1Of2 p) -> parameters1Tail (p::acc) (Span.merge span p.trivia) s
        // …
        | _ -> MultiType(List.rev acc, None) |> withTrivia span |> Ok

    /// varParameter | parameter ("," parameter)* ("," varParameter)?
    and parameters1 s =
        match parameterOrVarParameter s with
        | Error e -> Error e
        | Ok(Choice2Of2 v) -> MultiType([], Some v) |> withTrivia v.trivia |> Ok
        | Ok(Choice1Of2 p) -> parameters1Tail [p] p.trivia s

    /// "(" parameters1? ")"
    and parameters0 s =
        pipe3 (tokenSpan K.LBracket, option parameters1, tokenSpan K.RBracket) (fun (x1, x2, x3) ->
            match x2 with
            | None -> MultiType.empty |> withSpan2 x1 x3
            | Some x2 -> x2
        ) s

    /// parameter "," varParameter | parameter ("," parameter)+ ("," varParameter)?
    and parameters2 s =
        pipe3 (parameter, tokenSpan K.Comma, parameters1) (fun (p1, _, pt) ->
            match pt.kind with
            | MultiType(ps, v) -> MultiType(p1::ps, v) |> withSpan2 p1.trivia pt.trivia
            | _ -> failwithf "unreachable"
        ) s

    and results s = functionType s

    /// parameters0 ":" results
    and functionTypeTail n s =
        pipe3 (parameters0, tokenSpan K.Colon, results) (fun (ps, _, rs) ->
            FunctionType(ps, rs)
            |> withSpan2 (Name.measure n) rs.trivia
        ) s

    /// fieldKey ":" functionType
    and fieldSign s =
        pipe3 (fieldKey, colon, functionType) (fun (k, _, t) ->
            Field(k, t) |> withSpan2 k.trivia t.trivia
        ) s

    /// "{" field (fieldSep field)* fieldSep? "}"
    and fields s =
        pipe4 (tokenSpan K.LCBracket, sepBy fieldSep fieldSign, option fieldSep, tokenSpan K.RCBracket) (fun (l, fs, _, r) ->
            Fields(SepBy.toNonEmptyList fs)
            |> withSpan2 l r
        ) s

    and constraints s = fields s

    and interfaceType s =
        fields s |> mapResult (fun fs ->
            InterfaceType fs |> withTrivia fs.trivia
        )

    /// "(" type ")" | "(" ")"
    and wrappedType s =
        match tokenSpan K.LBracket s with
        | Error e -> Error e

        // "("
        | Ok span1 ->

        match Scanner.readTokenSpan K.RBracket s with

        // "(" ")"
        | ValueSome span2 -> MultiType.empty |> withSpan2 span1 span2 |> Ok

        // "(" …
        | _ -> pipe2 (typeSign, tokenSpan K.RBracket) (fun (t, _) -> t) s

    /// "[" "]"
    and arrayTypeTail t s = pipe2 (tokenSpan K.LSBracket, tokenSpan K.RSBracket) (fun (_, r) -> ArrayType t |> withSpan2 t.trivia r) s
    /// primitiveType ("[" "]")*
    and arrayType s = postfixOps primitiveType arrayTypeTail s
    /// ":" constraints
    and constrainedTypeTail t s = pipe2 (tokenSpan K.Colon, constraints) (fun (_, c) ->  ConstrainedType(t, c) |> withSpan2 t.trivia c.trivia) s
    /// arrayType ":" constraints
    and constrainedType s = postfixOps arrayType constrainedTypeTail s
    and functionType s = constrainedType s
    and multiType s =
        let s' = Scanner.getState s
        match parameters2 s with
        | Ok _ as r -> r
        | _ ->
            Scanner.setState &s' s
            functionType s

    and typeSign s = multiType s

    let restoreLastTokenAndTrivia ({ Scanner.currentTokenStructure = { hasValue = hasValue } } as s) =
        if hasValue then
            s.position <- s.currentTokenStructure._span.start

        s.currentTokenStructure <- Unchecked.defaultof<_>
        s.currentTokenStructure._kind <- K.Unknown
        s.remainingTriviaLength <- Scanner.skipTrivias s
        Scanner.readAndSetCurrentToken s

    let inline inSkipTriviaScope parse ({ Scanner.skipTrivia = oldSkipTrivia } as s) =
        s.skipTrivia <- true
        s.remainingTriviaLength <- Scanner.skipTrivias s
        Scanner.readAndSetCurrentToken s
        let r = parse s
        s.skipTrivia <- oldSkipTrivia
        if not oldSkipTrivia then
            restoreLastTokenAndTrivia s
        r

    let typeSignSkipTrivia s = inSkipTriviaScope typeSign s

    let typeTagTail at s =
        pipe2 (typeSignSkipTrivia, whiteSpaces0) (fun (t, _) -> TypeTag t |> withSpan2 at t.trivia) s

    let globalTagTail at s =
        pipe4 (whiteSpaces0, name, typeSignSkipTrivia, whiteSpaces0) (fun (_, n, t, _) -> GlobalTag(n, t) |> withSpan2 at t.trivia) s

    /// \s* name
    let featureTagTail at s =
        pipe3 (whiteSpaces0, name, whiteSpaces0) (fun (_, (Name name as n), _) -> FeatureTag n |> withSpan2 at name.trivia.span) s

    /// name (":" type)?
    let classTagTail at s =
        inSkipTriviaScope (pipe2 (name, option (pipe2 (tokenSpan K.Colon, typeSign) (fun (_, t) -> t))) (fun (Name name as n, t) ->
            let span2 =
                match t with
                | None -> name.trivia.span
                | Some t -> t.trivia

            ClassTag(n, t) |> withSpan2 at span2
        )) s

    let (|Visibility|) = function
        | "public" -> ValueSome Visibility.Public
        | "private" -> ValueSome Visibility.Private
        | "protected" -> ValueSome Visibility.Protected
        | _ -> ValueNone

    let visibility s =
        match Scanner.tokenKind s with
        | K.Name(Visibility(ValueSome v)) -> Scanner.skip s; Ok <| Some v
        | _ -> Ok None

    /// visibility? fieldKey type
    let fieldTagTail' at s = pipe3 (visibility, fieldKey, typeSign) (fun (v, n, t) -> FieldTag(v, n, t) |> withSpan2 at t.trivia) s
    let fieldTagTail at s = inSkipTriviaScope (fieldTagTail' at) s

    /// "..." constrainedType?
    let variadicTypeParameterTail n s =
        pipe2 (tokenSpan K.Dot3, option constrainedType) (fun (_, t) ->
            VariadicTypeParameter(n, t)
            |> withSpan2 (Name.measure n) (Span.option Source.measure t)
        ) s

    /// ":" constraints
    let typeParameterWithConstraintsTail n s =
        pipe2 (tokenSpan K.Colon, constraints) (fun (_, t) ->
            TypeParameter(n, Some t)
            |> withSpan2 (Name.measure n) t.trivia
        ) s

    /// name (":" constraints)? | name "..." constrainedType?
    let typeParameter s =
        match name s with
        | Error e -> Error e
        | Ok n ->

        match Scanner.tokenKind s with

        // name "..." …
        | K.Dot3 -> variadicTypeParameterTail n s

        // name ":" …
        | K.Colon -> typeParameterWithConstraintsTail n s

        // name …
        | _ -> TypeParameter(n, None) |> withTrivia (Name.measure n) |> Ok

    /// typeParameter ("," typeParameter)*
    let genericTagTail at s =
        inSkipTriviaScope (sepBy (tokenSpan K.Comma) typeParameter) s
        |> mapResult (fun xs ->
            xs
            |> SepBy.toNonEmptyList
            |> GenericTag
            |> withSpan2 at (SepBy.last xs).trivia
        )

    /// \s* \k<comments>
    let unknownTagTail at name s =
        pipe2 (whiteSpaces0, comments0) (fun (_, (Comment { trivia = commentSpan } as c)) ->
            UnknownTag(name, c)
            |> withSpan2 at commentSpan
        ) s

    /// "@" \k<name>
    let tagHead s = pipe2 (tokenSpan K.At, name) (fun (x1, x2) -> struct(x1, x2)) s

    /// (?<tag> @ \k<name> …)
    let tag s =
        match tagHead s with
        | Error e -> Error e
        | Ok(at, Name { kind = tagName } & n) ->

        match tagName with
        | "type" -> typeTagTail at s
        | "global" -> globalTagTail at s
        | "_Feature" -> featureTagTail at s
        | "class" -> classTagTail at s
        | "field" -> fieldTagTail at s
        | "generic" -> genericTagTail at s
        | _ -> unknownTagTail at n s

    /// (?<document> \k<comments> \k<tag>* )
    let document s =
        pipe2 (comments0, list tag) (fun (Comment { trivia = s1 } as c, tags) ->
            let s2 = Span.list Source.measure tags
            Document(c, tags) |> withSpan2 s1 s2
        ) s

    let rec triviasAsDocuments acc errors last s =
        if Scanner.skipIf Char.IsWhiteSpace s then triviasAsDocuments acc errors last s else

        if Scanner.readChar3 ('-', '-', '-') s then
            let p0 = Scanner.position s
            Scanner.skipCommentTail s
            let p1 = Scanner.position s
            initRange p0 (p1 - p0) s

            let acc, errors =
                match document s with
                | Error e -> [], e::errors
                | Ok x -> x::acc, []

            initRange p1 (last - p1) s
            triviasAsDocuments acc errors last s

        elif Scanner.readChar2 ('-', '-') s then
            match Scanner.longStringRange s with
            | ValueNone ->
                Scanner.skipCommentTail s
                triviasAsDocuments acc errors last s

            | ValueSome(start, length) ->
                let next = Scanner.position s

                initRange start length s
                let struct(acc, errors) = triviasAsDocuments acc errors (start + length) s

                initRange next (last - next) s
                triviasAsDocuments acc errors last s

        elif Scanner.isEos s then
            acc, errors
        else
            Scanner.unsafeAdvance s
            triviasAsDocuments acc errors last s

    let documents s position length =
        s |> Scanner.initWith (fun c -> { c with position = position; length = length; initialRead = false; skipTrivia = false }) s._source
        let struct(xs, es) = triviasAsDocuments [] [] (position + length) s
        struct(List.rev xs, List.rev es)
