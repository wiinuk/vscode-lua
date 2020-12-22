module LuaChecker.Parser
open Cysharp.Text
open LuaChecker.Syntaxes
open LuaChecker.Syntax
open LuaChecker.TolerantParserCombinator
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

module E = Errors

[<AutoOpen>]
module private Helpers =
    let inline withTrivia measure x = { kind = x; trivia = measure x }
    let withSpan2 start end' kind = { kind = kind; trivia = Span.merge start end' }
    let inline toTrivial make measure x = make x |> withTrivia measure
    let makeBinary (x1, x2, x3) = Binary(x1, x2, x3) |> withTrivia Exp.measure
    let varToPrefixExp x = withTrivia Var.measure x |> Var |> withTrivia PrefixExp.measure
    let functionCallToPrefixExp x = withTrivia FunctionCall.measure x |> Apply |> withTrivia PrefixExp.measure

    let inline sepBy isTerminator sep p s =
        let struct(x, xs) = sepBy isTerminator sep p s
        SepBy(x, xs)

    let token kind s =
        let t =
            match Scanner.readToken kind s with
            | ValueSome t -> t
            | _ ->
                Scanner.addErrorAtCurrentToken s <| Errors.findRequireToken kind
                Scanner.currentTokenToTrivia s

        { kind = HEmpty; trivia = t }

    let isToken predicate s = predicate (Scanner.tokenKind s)
    let eqToken token s = Scanner.tokenKind s = token
    let notEqualsToken token s = Scanner.tokenKind s <> token

    let missingArgs trivia =
        let t = { kind = HEmpty; trivia = trivia }
        Args(t, None, t) |> withTrivia Args.measure

    let missingVarOf trivia name =
        { kind = name; trivia = trivia }
        |> Name
        |> Variable
        |> withTrivia Var.measure

    let missingVar trivia = missingVarOf trivia ""

    let readAnyTokenToMissingPrefixExp s =
        let missingVar =
            match Scanner.read s with
            | ValueNone -> missingVar <| Scanner.positionToTrivia s
            | ValueSome t ->

            Printer.showKind Printer.PrintConfig.defaultConfig t.kind
            |> String.concat ""
            |> missingVarOf t.trivia

        Var missingVar
        |> withTrivia PrefixExp.measure

    let readAnyTokenToMissingCall s =
        let t = Scanner.currentTokenToTrivia s
        let missingExp = readAnyTokenToMissingPrefixExp s

        Call(missingExp, missingArgs t)
        |> withTrivia FunctionCall.measure
        |> FunctionCall

    let isBlockTerminator = function
        | K.Semicolon
        | K.Unknown
        | K.End
        | K.Until
        | K.ElseIf
        | K.Else -> true
        | _ -> false

    let isLastStatInitiator = function
        | K.Return
        | K.Break -> true
        | _ -> false

    let optionalToken k s =
        match Scanner.readPick (fun x -> if x = k then ValueSome x else ValueNone) s with
        | ValueSome(_, k) -> Some { kind = HEmpty; trivia = k }
        | _ -> None

    let hasLeadingNewLine s =
        let s' = Scanner.peek s
        if s'._kind = K.Unknown then false else

        let leadingTriviaLength = s'._leadingTriviaLength
        1 <= leadingTriviaLength && 0 <= s._source.IndexOf('\n', s'._span.start - leadingTriviaLength, leadingTriviaLength)

    let isCallOpInitiator s =
        match Scanner.tokenKind s with
        | K.LSBracket
        | K.Dot
        | K.Colon
        | K.String _
        | K.LCBracket -> true
        | K.LBracket -> not <| hasLeadingNewLine s
        | _ -> false

let name s =
    match Scanner.readPick (function K.Name x -> ValueSome x | _ -> ValueNone) s with
    | ValueSome(x, t) -> Name { kind = x; trivia = t }
    | _ ->
        Scanner.addErrorAtCurrentToken s E.RequireName
        Name { kind = ""; trivia = Scanner.currentTokenToTrivia s }

let stringArg s =
    match Scanner.readPick (function K.String x -> ValueSome x | _ -> ValueNone) s with
    | ValueSome(x, t) -> StringLiteral { kind = x; trivia = t } |> StringArg |> withTrivia Args.measure
    | _ ->
        Scanner.addErrorAtCurrentToken s E.RequireString
        missingArgs <| Scanner.currentTokenToTrivia s

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
    | ValueSome(k, t) -> Literal { kind = k; trivia = t }
    | _ ->
        Scanner.addErrorAtCurrentToken s E.RequireLiteral
        Scanner.currentTokenToTrivia s
        |> missingVar
        |> Var
        |> withTrivia PrefixExp.measure
        |> PrefixExp

let fieldSep s =
    match Scanner.readPick (function FieldSepKind(ValueSome k) -> ValueSome k | _ -> ValueNone) s with
    | ValueSome(k, t) -> { kind = k; trivia = t }
    | _ ->
        Scanner.addErrorAtCurrentToken s E.RequireFieldSep
        { kind = Comma; trivia = Scanner.currentTokenToTrivia s }

let unaryOp s =
    match Scanner.readPick (function UnaryOpKind(ValueSome k) -> ValueSome k | _ -> ValueNone) s with
    | ValueSome(k, t) -> { kind = k; trivia = t }
    | _ ->
        Scanner.addErrorAtCurrentToken s E.RequireUnaryOp
        { kind = Len; trivia = Scanner.currentTokenToTrivia s }

/// name (, name)*
let nameList s = sepBy (notEqualsToken K.Comma) comma name s |> withTrivia (Span.sepBy Name.measure)

/// name (. name)* (: name)?
let funcName s =
    FuncName(
        name s,
        list (notEqualsToken K.Dot) (tuple2 (dot, name)) s,
        option (eqToken K.Colon) (tuple2 (colon, name)) s
    )
    |> withTrivia FuncName.measure

/// name (, name)* (, ...)?
let inline namesParameterList s =
    let name1 = name s
    let mutable commaAndNamesRev = []
    let mutable commaAndDot3 = None
    while
        match Scanner.tokenKind s with
        | K.Comma ->
            let comma = comma s
            match Scanner.tokenKind s with
            | K.Name _ -> commaAndNamesRev <- (comma, name s)::commaAndNamesRev; true
            | K.Dot3 -> commaAndDot3 <- Some(comma, dot3 s); false
            | _ -> Scanner.addErrorAtCurrentToken s E.RequireNameOrDot3; true
        | _ -> false
        do ()

    let names = SepBy(name1, List.rev commaAndNamesRev)
    let names = { kind = names; trivia = Span.sepBy Name.measure names }
    ParameterList(names, commaAndDot3)

let varParameterList s = dot3 s |> VarParameter
let inline parameterList s =
    match Scanner.tokenKind s with
    | K.Dot3 -> varParameterList s
    | _ -> namesParameterList s
    |> withTrivia ParameterList.measure

let inline binaryOp missingOpKind (|OpKind|) s =
    match Scanner.readPick (function OpKind x -> x) s with
    | ValueSome(k, t) -> { kind = k; trivia = t }
    | _ ->
        Scanner.addErrorAtCurrentToken s E.RequireBinaryOp
        { kind = missingOpKind; trivia = Scanner.currentTokenToTrivia s }

let mulOp s = binaryOp Mul (|MulOpKind|) s
let addOp s = binaryOp Add (|AddOpKind|) s
let relationalOp s = binaryOp Eq (|RelationalOpKind|) s
let andOp s = binaryOp And (function K.And -> ValueSome And | _ -> ValueNone) s
let orOp s = binaryOp Or (function K.Or -> ValueSome Or | _ -> ValueNone) s
let powOp s = binaryOp Pow (function K.Pow -> ValueSome Pow | _ -> ValueNone) s
let conOp s = binaryOp Con (function K.Con -> ValueSome Con | _ -> ValueNone) s

let rec functionExp s = Function(function' s, funcBody s)
and primExp s =
    match Scanner.tokenKind s with
    | K.Dot3 -> VarArg(dot3 s)
    | K.Function -> functionExp s
    | K.LCBracket -> NewTable(tableConstructor s)
    | K.Nil
    | K.True
    | K.False
    | K.Number _
    | K.String _ -> literal s
    | _ -> PrefixExp(prefixExp s)
    |> withTrivia Exp.measure

and powExp s = chainR (notEqualsToken K.Pow) primExp powOp makeBinary s
and unaryExp s = prefixOps (isToken ((|UnaryOpKind|) >> ValueOption.isNone)) (fun (op, x) -> Unary(op, x) |> withTrivia Exp.measure) unaryOp powExp s
and mulExp s = chainL (isToken ((|MulOpKind|) >> ValueOption.isNone)) unaryExp mulOp (toTrivial Binary Exp.measure) s
and addExp s = chainL (isToken ((|AddOpKind|) >> ValueOption.isNone)) mulExp addOp makeBinary s
and concatExp s = chainR (notEqualsToken K.Con) addExp conOp makeBinary s
and relationalExp s = chainL (isToken ((|RelationalOpKind|) >> ValueOption.isNone)) concatExp relationalOp makeBinary s
and andExp s = chainL (notEqualsToken K.And) relationalExp andOp makeBinary s
and orExp s = chainL (notEqualsToken K.Or) andExp orOp makeBinary s
and exp s = orExp s

and expList s = sepBy (notEqualsToken K.Comma) comma exp s |> withTrivia (Span.sepBy Source.measure)

and indexInit s = IndexInit(lsBracket s, exp s, rsBracket s, assign s, exp s)
and memberInitTail x1 s = MemberInit(x1, assign s, exp s)
and field s =
    match Scanner.tokenKind s with
    | K.Unknown ->
        Scanner.addErrorAtCurrentToken s E.RequireAnyField

        Scanner.currentTokenToTrivia s
        |> missingVar
        |> Var
        |> withTrivia PrefixExp.measure
        |> PrefixExp
        |> withTrivia Exp.measure
        |> Init

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
            Init(exp s)

    | _ -> Init(exp s)
    |> withTrivia Field.measure

and inline fieldList isTerminator s =
    let f1 = field s
    let mutable sepAndFieldsRev = []
    let mutable lastSep = None
    while
        begin
            if isTerminator s || Scanner.tokenKind s = K.Unknown then false else
            let sep = fieldSep s

            if isTerminator s || Scanner.tokenKind s = K.Unknown then
                lastSep <- Some sep
                false

            else
                sepAndFieldsRev <- (sep, field s)::sepAndFieldsRev
                true
        end
        do ()

    FieldList(SepBy(f1, List.rev sepAndFieldsRev), lastSep)

and tableConstructor s =
    TableConstructor(
        token K.LCBracket s,
        option (isToken (function K.RCBracket | K.Unknown -> false | _ -> true)) (fieldList (eqToken K.RCBracket)) s,
        token K.RCBracket s
    )
    |> withTrivia TableConstructor.measure

and wrappedArgs s =
    if hasLeadingNewLine s then
        Scanner.addErrorAtCurrentToken s E.DisallowedLeadingNewLine
        missingArgs <| Scanner.currentTokenToTrivia s
    else
        Args(lBracket s, option (isToken (function K.RBracket | K.Unknown -> false | _ -> true)) expList s, rBracket s)
        |> withTrivia Args.measure

and args s =
    match Scanner.tokenKind s with
    | K.String _ -> stringArg s
    | K.LCBracket -> TableArg(tableConstructor s) |> withTrivia Args.measure
    | _ -> wrappedArgs s

and varTail x1 s =
    match Scanner.tokenKind s with
    | K.LSBracket -> Index(x1, lsBracket s, exp s, rsBracket s)
    | _ -> Member(x1, dot s, name s)
    |> varToPrefixExp

and functionCallTail x1 s =
    match Scanner.tokenKind s with
    | K.Colon ->
        let colon = colon s
        let name = name s
        match Scanner.tokenKind s with

        // `exp : name \n (`
        | K.LBracket when hasLeadingNewLine s ->
            Scanner.addErrorAtCurrentToken s E.DisallowedLeadingNewLine

        | _ -> ()
        let args = args s

        CallWithSelf(x1, colon, name, args) |> functionCallToPrefixExp

    // `exp \n (`
    | K.LBracket when hasLeadingNewLine s -> x1

    | _ -> Call(x1, args s) |> functionCallToPrefixExp

and primPrefixExp s =
    match Scanner.tokenKind s with
    | K.LBracket -> Wrap(lBracket s, exp s, rBracket s) |> withTrivia PrefixExp.measure
    | K.Name _ -> Variable(name s) |> varToPrefixExp
    | _ ->
        Scanner.addErrorAtCurrentToken s E.RequireNameOrLBracket
        readAnyTokenToMissingPrefixExp s

/// `primPrefixExp = name | '(' exp ')'`
/// `callOp = '[' exp ']' | '.' name | args | ':' name args`
/// `prefixExp = primPrefixExp callOp*`
and callOp x s =
    match Scanner.tokenKind s with
    | K.LSBracket
    | K.Dot -> varTail x s
    | _ -> functionCallTail x s

and prefixExp s = postfixOps (isCallOpInitiator >> not) primPrefixExp callOp s

and funcBody s =
    FuncBody(
        lBracket s,
        option (isToken (function K.Name _ | K.Dot3 -> true | _ -> false)) parameterList s,
        rBracket s,
        block s,
        token K.End s
    )
    |> withTrivia FuncBody.measure

and returnStat s =
    Return(
        token K.Return s,
        option (isToken (isBlockTerminator >> not)) expList s
    )
and lastStat s =
    match Scanner.tokenKind s with
    | K.Return -> returnStat s
    | _ -> Break(token K.Break s)
    |> withTrivia LastStat.measure

and elseIfClause s = ElseIf(token K.ElseIf s, exp s, then' s, block s) |> withTrivia ElseIf.measure
and elseClause s = Else(token K.Else s, block s) |> withTrivia Else.measure

and doStat s = Do(do' s, block s, end' s)
and whileStat s = While(token K.While s, exp s, do' s, block s, end' s)
and repeatUntilStat s = RepeatUntil(token K.Repeat s, block s, token K.Until s, exp s)
and ifStat s =
    If(
        token K.If s, exp s,
        then' s, block s,
        list (notEqualsToken K.ElseIf) elseIfClause s,
        option (eqToken K.Else) elseClause s,
        end' s
    )
and forAssignStateTail for' name s =
    For(
        for', name, assign s, exp s, comma s, exp s,
        option (eqToken K.Comma) (tuple2 (comma, exp)) s,
        do' s, block s, end' s
    )

/// (, \k<name>)* in \k<expList> do \k<block> end
and forInStatTail for' name1 s =
    let names = list (notEqualsToken K.Comma) (tuple2 (comma, name)) s
    let nameList = SepBy(name1, names) |> withTrivia (Span.sepBy Name.measure)
    ForIn(for', nameList, token K.In s, expList s, do' s, block s, end' s)

and forAssignOrForInStat s =
    let for' = for' s
    let name1 = name s
    match Scanner.tokenKind s with
    | K.Assign -> forAssignStateTail for' name1 s
    | _ -> forInStatTail for' name1 s

and functionStat s = FunctionDecl(function' s, funcName s, funcBody s)
and localFunctionStatTail x1 s = LocalFunction(x1, function' s, name s, funcBody s)
and localStatTail x1 s =
    Local(
        x1,
        nameList s,
        option (eqToken K.Assign) (tuple2(assign, expList)) s
    )
and localStat s =
    let t = token K.Local s
    match Scanner.tokenKind s with
    | K.Function -> localFunctionStatTail t s
    | _ -> localStatTail t s

and var s =
    match prefixExp s with
    | { kind = Var x1 } -> x1
    | _ ->
        Scanner.addErrorAtCurrentToken s E.RequireVar
        missingVar <| Scanner.currentTokenToTrivia s

and assignStatTail (state: _ inref) var1 s =
    match Scanner.tokenKind s with
    | K.Assign
    | K.Comma ->
        let vars = list (notEqualsToken K.Comma) (tuple2 (comma, var)) s
        let vars = SepBy(var1, vars) |> withTrivia (Span.sepBy Source.measure)
        Assign(vars, assign s, expList s)
    | _ ->
        Scanner.setState &state s
        Scanner.addErrorAtCurrentToken s E.RequireAssignStatOrFunctionCall
        readAnyTokenToMissingCall s

/// ```regexp
/// \k<var> (, \k<var>)* = \k<exp> (, \k<exp>)* | \k<functionCall>
/// ```
and assignStatOrFunctionCallStat s =
    let state = Scanner.getState s
    let exp1 = prefixExp s
    match exp1.kind with
    | Var var1 -> assignStatTail &state var1 s
    | Apply functionCall -> FunctionCall functionCall
    | _ ->
        Scanner.setState &state s
        Scanner.addErrorAtCurrentToken s E.RequireAssignStatOrFunctionCall
        readAnyTokenToMissingCall s

and stat s =
    match Scanner.tokenKind s with
    | K.Unknown ->
        Scanner.addErrorAtCurrentToken s E.RequireAnyStat
        let trivia = Scanner.positionToTrivia s
        let var = missingVar trivia
        Call(varToPrefixExp var.kind, missingArgs trivia)
        |> withTrivia FunctionCall.measure
        |> FunctionCall

    | K.Do -> doStat s
    | K.While -> whileStat s
    | K.Repeat -> repeatUntilStat s
    | K.If -> ifStat s
    | K.For -> forAssignOrForInStat s
    | K.Function -> functionStat s
    | K.Local -> localStat s
    | _ -> assignStatOrFunctionCallStat s

    |> withTrivia Stat.measure

and blockStats s =
    list
        (isToken (fun k -> isLastStatInitiator k || isBlockTerminator k))
        (tuple2 (stat, optionalToken K.Semicolon))
        s

and blockLastStat s = option (isToken isLastStatInitiator) (tuple2 (lastStat, optionalToken K.Semicolon)) s
and block s =
    let x1 = blockStats s
    let x2 = blockLastStat s
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

    { kind = b; trivia = trivia }

and sourceFile s =
    let b = block s
    if Scanner.tokenKind s <> K.Unknown then
        Scanner.addErrorAtCurrentToken s E.RequireEndOfSource
    b

module private DocumentParserHelpers =
    open System
    open LuaChecker.ParserCombinator
    open LuaChecker.Syntax.Documents

    module Annotated =
        let inline measure f (Annotated(x, _)) = f x

    module Measure =
        let annotated (Annotated({ trivia = x }, _)) = x
        let identifier (Annotated(Name { trivia = { span = x } }, _)) = x

        let parameters (Parameters ps) =
            Span.sepBy Source.measure ps

    module Fields =
        open Measure
        let measure (Fields(l, _, _, r)) = Span.merge (annotated l) (annotated r)

    module TypeSign =
        open Measure
        let measure = function
            | EmptyType(l, r) -> Span.merge (annotated l) (annotated r)
            | ArrayType(l, _, r) -> Span.merge l.trivia (annotated r)
            | ConstrainedType(l, _, r) -> Span.merge l.trivia r.trivia
            | FunctionType(l, _, _, _, _, r) -> Span.merge (annotated l) r.trivia
            | InterfaceType x -> x.trivia
            | MultiType2(l, _, r) -> Span.merge l.trivia (parameters r)
            | NamedType(l, None) -> identifier l
            | NamedType(l, Some(GenericArguments(_, _, _, r))) -> Span.merge (identifier l) (annotated r)
            | SingleMultiType(l, _, _, r) -> Span.merge (annotated l) (annotated r)
            | VariadicType { trivia = t } -> t
            | WrappedType(l, _, r) -> Span.merge (annotated l) (annotated r)

    module Parameter =
        let measure (Parameter(l, r)) =
            match l with
            | Some(l, _) -> Span.merge (Measure.identifier l) r.trivia
            | _ -> r.trivia

    module TagTail =
        let measure = function
            | TypeTag(l, r) -> Span.merge (Measure.annotated l) r.trivia
            | GlobalTag(l, _, r) -> Span.merge (Measure.annotated l) r.trivia
            | FeatureTag(l, r) -> Span.merge (Measure.annotated l) (Measure.identifier r)
            | ClassTag(l, r, None) -> Span.merge (Measure.annotated l) (Measure.identifier r)
            | ClassTag(l, _, Some(_, r)) -> Span.merge (Measure.annotated l) r.trivia
            | FieldTag(l, _, _, r) -> Span.merge (Measure.annotated l) r.trivia
            | GenericTag(l, r) -> Span.merge (Measure.annotated l) (Span.sepBy Source.measure r)
            | UnknownTag(l, Comment r) -> Span.merge (Measure.identifier l) r.trivia

    let withTrivia trivia k = { kind = k; trivia = trivia }
    let inline withMeasuredTrivia measure k = { kind = k; trivia = measure k }
    let withEmptyAnnotation target = Annotated(target, HEmpty)

    let token kind s =
        match Scanner.readTokenSpan kind s with
        | ValueSome t -> Ok(withEmptyAnnotation { kind = HEmpty; trivia = t })
        | _ -> Error <| Errors.findRequireToken kind

    let colon s = token K.Colon s

    let fieldSep s =
        match Scanner.tokenKind s with
        | FieldSepKind(ValueSome k) -> { kind = k; trivia = Scanner.unsafeReadSpan s } |> withEmptyAnnotation |> Ok
        | _ -> Error E.RequireFieldSep

    let name s =
        match Scanner.readPick (function K.Name x -> ValueSome x | _ -> ValueNone) s with
        | ValueSome(x, t) -> Name { kind = x; trivia = t } |> withEmptyAnnotation |> Ok
        | _ -> Error E.RequireName

    let inline sepBy sep p s = sepBy sep p s |> mapResult (fun struct(x, xs) -> SepBy(x, xs))

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
    type private K = TokenKind
    type private E = Syntax.ParseError
    open LuaChecker
    open LuaChecker.ParserCombinator
    open LuaChecker.Syntax.Documents
    open System
    open DocumentParserHelpers
    open type LuaChecker.Syntax.Name<HEmpty voption>

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

    let rec primitiveType s =
        match Scanner.tokenKind s with
        | K.Name n ->
            let n' = n |> withTrivia (Scanner.unsafeReadTrivia s) |> Syntax.Name |> withEmptyAnnotation

            match Scanner.tokenKind s with
            // name "<" …
            | K.Lt -> genericTypeTail n' s
            // name "..." …
            | K.Dot3 -> varParameterTail (Some n') s |> mapResult (fun v -> VariadicType v |> withTrivia v.trivia)
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
        | K.Dot3 -> varParameterTail None s |> mapResult (fun v -> VariadicType v |> withTrivia v.trivia)

        | _ -> Error E.RequireAnyTypeSign

    /// name? "..." primitiveType?
    and varParameterTail n s =
        let dot3 = withTrivia (Scanner.unsafeReadSpan s) HEmpty |> withEmptyAnnotation

        option primitiveType s
        |> mapResult (fun et ->
            let span = Span.merge (Span.option (Annotated.measure Name.measure) n) (Annotated.measure Source.measure dot3)
            VariadicTypeSign(n, dot3, et)
            |> withSpan2 span (Span.option Source.measure et)
        )

    /// "(" parameter "," ")"
    and multiType1 s =
        pipe4 (token K.LBracket, parameter, token K.Comma, token K.RBracket) (fun (l, t, c, r) ->
            SingleMultiType(l, t, c, r)
            |> withMeasuredTrivia TypeSign.measure
        ) s

    /// name ":" constrainedType | "..." constrainedType? | constrainedType
    and parameter s =
        match Scanner.tokenKind s with
        | K.Name n ->
            let s' = Scanner.getState s
            let nt = Scanner.unsafeReadTrivia s
            let n = n |> withTrivia nt |> Syntax.Name |> withEmptyAnnotation

            match Scanner.tokenKind s with
            // name ":" …
            | K.Colon -> namedParameterTail n s

            // name …
            | _ ->
                Scanner.setState &s' s
                namelessParameter s

        | _ -> namelessParameter s

    and namedType n = NamedType(n, None) |> withMeasuredTrivia TypeSign.measure |> Ok

    /// "<" constrainedType ("," constrainedType)* ","? ">"
    and genericTypeTail n s =
        pipe4 (token K.Lt, sepBy (token K.Comma) constrainedType, option (token K.Comma), token K.Gt) (fun (lt, ts, s, gt) ->
            NamedType(n, Some(GenericArguments(lt, ts, s, gt)))
            |> withMeasuredTrivia TypeSign.measure
        ) s

    /// ":" constrainedType
    and namedParameterTail n s =
        let colon = HEmpty |> withTrivia (Scanner.unsafeReadSpan s) |> withEmptyAnnotation
        constrainedType s
        |> mapResult (fun t ->
            Parameter(Some(n, colon), t)
            |> withMeasuredTrivia Parameter.measure
        )

    /// functionType
    and namelessParameter s =
        functionType s
        |> mapResult (fun t ->
            Parameter(None, t) |> withTrivia t.trivia
        )

    /// parameter ("," parameter)*
    and parameters1 s = sepBy (token K.Comma) parameter s |> mapResult Parameters

    /// parameter ("," parameter)+
    and parameters2 s =
        pipe3 (parameter, token K.Comma, parameters1) (fun (p, c, ps) ->
            let (Parameters ps') = ps
            let span = Span.sepBy Source.measure ps'

            MultiType2(p, c, ps)
            |> withSpan2 p.trivia span
        ) s

    and results s = functionType s

    /// fieldKey ":" constrainedType
    and fieldSign s =
        pipe3 (fieldKey, colon, constrainedType) (fun (k, c, t) ->
            Field(k, c, t) |> withSpan2 k.trivia t.trivia
        ) s

    /// "{" field (fieldSep field)* fieldSep? "}"
    and fields s =
        pipe4 (token K.LCBracket, sepBy fieldSep fieldSign, option fieldSep, token K.RCBracket) (fun (l, fs, s, r) ->
            Fields(l, fs, s, r)
            |> withMeasuredTrivia Fields.measure
        ) s

    and constraints s = fields s

    and interfaceType s =
        fields s |> mapResult (fun fs ->
            InterfaceType fs |> withTrivia fs.trivia
        )

    /// "(" type ")" | "(" ")"
    and wrappedType s =
        match token K.LBracket s with
        | Error e -> Error e

        // "("
        | Ok l ->

        match token K.RBracket s with

        // "(" ")"
        | Ok r -> EmptyType(l, r) |> withMeasuredTrivia TypeSign.measure |> Ok

        // "(" …
        | _ -> pipe2 (typeSign, token K.RBracket) (fun (t, r) -> WrappedType(l, t, r) |> withMeasuredTrivia TypeSign.measure) s

    /// "[" "]"
    and arrayTypeTail t s = pipe2 (token K.LSBracket, token K.RSBracket) (fun (l, r) -> ArrayType(t, l, r) |> withMeasuredTrivia TypeSign.measure) s
    /// primitiveType ("[" "]")*
    and arrayType s = postfixOps primitiveType arrayTypeTail s
    and makeFunctionType (struct(funName, l, ps, r, c), t) =
        FunctionType(funName, l, ps, r, c, t)
        |> withMeasuredTrivia TypeSign.measure
    and functionTypeHeadTail funNameTrivia s =
        pipe4 (token K.LBracket, option parameters1, token K.RBracket, colon) (fun (l, ps, r, c) ->
            let funName = HEmpty |> withTrivia funNameTrivia |> withEmptyAnnotation
            struct(funName, l, ps, r, c)
        ) s
    /// "fun" "(" parameters1? ")" ":"
    and functionTypeHead s =
        let state = Scanner.getState s
        match Scanner.tokenKind s with
        | K.Name n when n = "fun" ->
            let funNameTrivia = Scanner.unsafeReadSpan s

            match Scanner.tokenKind s with

            // "fun" "(" …
            | K.LBracket -> functionTypeHeadTail funNameTrivia s

            | _ ->
                Scanner.setState &state s
                Error <| E.findRequireToken K.LBracket
        | _ -> Error E.RequireName

    /// ("fun" "(" parameters1? ")" ":")* arrayType
    and functionType s = prefixOps makeFunctionType functionTypeHead arrayType s
    /// ":" constraints
    and constrainedTypeTail t s = pipe2 (colon, constraints) (fun (colon, c) -> ConstrainedType(t, colon, c) |> withSpan2 t.trivia c.trivia) s
    /// functionType (":" constraints)*
    and constrainedType s = postfixOps functionType constrainedTypeTail s
    /// parameters2 / constrainedType
    and multiType s =
        let s' = Scanner.getState s
        match parameters2 s with
        | Ok _ as r -> r
        | _ ->
            Scanner.setState &s' s
            constrainedType s

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

    let typeTag tagName s =
        pipe2 (typeSignSkipTrivia, whiteSpaces0) (fun (t, _) ->
            TypeTag(tagName, t)
            |> withMeasuredTrivia TagTail.measure
        ) s

    let globalTag tagName s =
        pipe4 (whiteSpaces0, name, typeSignSkipTrivia, whiteSpaces0) (fun (_, n, t, _) ->
            GlobalTag(tagName, n, t)
            |> withMeasuredTrivia TagTail.measure
        ) s

    /// \s* name
    let featureTag tagName s =
        pipe3 (whiteSpaces0, name, whiteSpaces0) (fun (_, n, _) ->
            FeatureTag(tagName, n)
            |> withMeasuredTrivia TagTail.measure
        ) s

    /// name (":" type)?
    let classTag tagName s =
        inSkipTriviaScope (pipe2 (name, option (pipe2 (colon, typeSign) id)) (fun (n, t) ->
            ClassTag(tagName, n, t)
            |> withMeasuredTrivia TagTail.measure
        )) s

    let (|Visibility|) = function
        | "public" -> ValueSome Visibility.Public
        | "private" -> ValueSome Visibility.Private
        | "protected" -> ValueSome Visibility.Protected
        | _ -> ValueNone

    let visibility s =
        match Scanner.tokenKind s with
        | K.Name(Visibility(ValueSome v)) ->
            let span = Scanner.tokenSpan s
            Scanner.skip s
            v
            |> withTrivia span
            |> Some
            |> Ok

        | _ -> Ok None

    /// visibility? fieldKey type
    let fieldTagTail' tagName s =
        pipe3 (visibility, fieldKey, typeSign) (fun (v, n, t) ->
            FieldTag(tagName, v, n, t)
            |> withMeasuredTrivia TagTail.measure
        ) s
    let fieldTag tagName s = inSkipTriviaScope (fieldTagTail' tagName) s

    /// "..." primitiveType?
    let variadicTypeParameterTail n s =
        pipe2 (token K.Dot3, option primitiveType) (fun (dot3, t) ->
            VariadicTypeParameter(n, dot3, t)
            |> withSpan2 (Measure.identifier n) (Span.option Source.measure t)
        ) s

    /// ":" constraints
    let typeParameterWithConstraintsTail n s =
        pipe2 (colon, constraints) (fun (colon, t) ->
            TypeParameter(n, Some(colon, t))
            |> withSpan2 (Measure.identifier n) t.trivia
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
        | _ -> TypeParameter(n, None) |> withTrivia (Measure.identifier n) |> Ok

    /// typeParameter ("," typeParameter)*
    let genericTag tagName s =
        inSkipTriviaScope (sepBy (token K.Comma) typeParameter) s
        |> mapResult (fun xs ->
            GenericTag(tagName, xs)
            |> withMeasuredTrivia TagTail.measure
        )

    /// \s* \k<comments>
    let unknownTagTail tagName s =
        pipe2 (whiteSpaces0, comments0) (fun (_, c) ->
            UnknownTag(tagName, c)
            |> withMeasuredTrivia TagTail.measure
        ) s

    /// "@" \k<name>
    let tagHead s = pipe2 (token K.At, name) (fun (x1, x2) -> struct(x1, x2)) s

    /// (?<tag> @ \k<name> …)
    let tag s =
        match tagHead s with
        | Error e -> Error e
        | Ok(at, Annotated(Name.Name tagName, _)) ->

        let n = HEmpty |> withTrivia tagName.trivia.span |> withEmptyAnnotation
        match tagName.kind with
        | "type" -> typeTag n s
        | "global" -> globalTag n s
        | "_Feature" -> featureTag n s
        | "class" -> classTag n s
        | "field" -> fieldTag n s
        | "generic" -> genericTag n s
        | _ -> unknownTagTail (Syntax.Name tagName |> withEmptyAnnotation) s

        |> mapResult (fun e ->
            Tag(at, e)
            |> withSpan2 (Measure.annotated at) e.trivia
        )

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
