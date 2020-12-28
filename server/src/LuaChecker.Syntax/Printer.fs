module LuaChecker.Syntax.Printer
open LuaChecker
open LuaChecker.Syntax
open LuaChecker.Syntaxes
open System

type private K = Syntax.TokenKind

type NumberStyle =
    | Decimal
    | Hex

type StringStyle =
    | SingleQuote
    | DoubleQuote
    | LongString

type EscapeLevel =
    | Min
    | Control
    | Max

type PrintConfig = {
    numberStyle: NumberStyle
    stringStyle: StringStyle
    longStringEqCount: int
    charEscape: EscapeLevel
}
module PrintConfig =
    let defaultConfig = {
        numberStyle = Decimal
        stringStyle = DoubleQuote
        longStringEqCount = 0
        charEscape = Min
    }

let escapeChar (x: string) i = seq {
    let isDigit i x = i < String.length x && Scanner.isDigit x.[i]

    match x.[i] with
    | '\\' -> "\\\\"
    | '"' -> "\\\""
    | '\'' -> "\\'"
    | '\a' -> "\\a"
    | '\b' -> "\\b"
    | '\f' -> "\\f"
    | '\n' -> "\\n"
    | '\r' -> "\\r"
    | '\t' -> "\\t"
    | c ->
        "\\"
        if int c <= 9 && isDigit (i + 1) x then "00"
        if 9 < int c && int c <= 99 && isDigit (i + 1) x then "0"
        string (int c)
}
let isRequireEscape stringStyle charEscape struct(x, i) =
    match (x: string).[i], stringStyle, charEscape with

    // required
    | '\\', (SingleQuote | DoubleQuote), _
    | '"', DoubleQuote, _
    | '\'', SingleQuote, _ -> true

    // control
    | c, (SingleQuote | DoubleQuote), escape when Control <= escape && Char.IsControl c && int c <= 999 -> true

    // max
    | c, (SingleQuote | DoubleQuote), escape when Max <= escape && int c <= 999 -> true

    | _ -> false

let charsCore requireEscape x = seq {
    for i = 0 to String.length x - 1 do
        let c = x.[i]
        if requireEscape struct(x, i) then yield! escapeChar x i else
        string c
}
let rec safeEqCount x count =
    let quote = "]" + String('=', count)
    if (x + "").Contains quote then safeEqCount x (count + 1)
    else count

let repeat x count = seq { for _ in 1..count -> x }
let eqs = repeat "="
let inline showStringCore stringStyle longStringEqCount requireEscape x = seq {
    match stringStyle with
    | SingleQuote -> "'"; yield! charsCore requireEscape x; "'"
    | DoubleQuote -> "\""; yield! charsCore requireEscape x; "\""
    | LongString ->
        let eq = safeEqCount x <| max 0 longStringEqCount

        "["; yield! eqs eq; "["
        if 1 <= x.Length && 0 = x.IndexOf('\n', 0, 1) then "\n"
        if x.StartsWith "\r\n" then "\r\n"
        yield! charsCore requireEscape x
        "]"; yield! eqs eq; "]"
}
let showString config x = showStringCore config.stringStyle config.longStringEqCount (isRequireEscape config.stringStyle config.charEscape) x
let showNumberCore numberStyle x =
    match numberStyle with
    | Hex when double (int x) = x -> sprintf "0x%X" <| int x
    | Hex
    | Decimal -> sprintf "%.17g" x

let showNumber config x = showNumberCore config.numberStyle x

let showKind config k = seq {
    match k with
    | K.Unknown -> failwith ""

    | K.Name x -> x
    | K.Number x -> showNumber config x
    | K.String x -> yield! showString config x

    | K.Comma -> ","
    | K.Dot -> "."
    | K.Dot3 -> "..."
    | K.Function -> "function"
    | K.End -> "end"
    | K.Return -> "return"
    | K.Break -> "break"
    | K.If -> "if"
    | K.Then -> "then"
    | K.ElseIf -> "elseif"
    | K.Else -> "else"
    | K.While -> "while"
    | K.Do -> "do"
    | K.Repeat -> "repeat"
    | K.Until -> "until"
    | K.For -> "for"
    | K.In -> "in"
    | K.Local -> "local"

    | K.LSBracket -> "["
    | K.RSBracket -> "]"
    | K.LCBracket -> "{"
    | K.RCBracket -> "}"
    | K.LBracket -> "("
    | K.RBracket -> ")"
    | K.Assign -> "="
    | K.Colon -> ":"
    | K.Semicolon -> ";"
    | K.Add -> "+"
    | K.Sub -> "-"
    | K.Mul -> "*"
    | K.Div -> "/"
    | K.Pow -> "^"
    | K.Mod -> "%"
    | K.Con -> ".."
    | K.Lt -> "<"
    | K.Le -> "<="
    | K.Gt -> ">"
    | K.Ge -> ">="
    | K.Eq -> "=="
    | K.Ne -> "~="
    | K.And -> "and"
    | K.Or -> "or"

    | K.Not -> "not"
    | K.Len -> "#"

    | K.Nil -> "nil"
    | K.True -> "true"
    | K.False -> "false"

    // documentation comment
    | K.At -> "@"
}
[<Struct>]
type PrintEnv<'T,'S> = {
    config: PrintConfig
    printToken: struct (PrintConfig * Token<TokenKind,'T>) -> 'S seq
}

let withKind env kind { trivia = t } = env.printToken(env.config, { kind = kind; trivia = t })

let option printer x = seq {
    match x with
    | None -> ()
    | Some x -> yield! printer x
}
let tuple2 (p1, p2) (x1, x2) = seq {
    yield! p1 x1
    yield! p2 x2
}
let sepBy sepP p (SepBy(x, tail)) = seq {
    yield! p x
    for sep, x in tail do
        yield! sepP sep
        yield! p x
}
let token env kind x = withKind env kind x

let name env (Name x) = withKind env (K.Name x.kind) x

let rec exp env x = seq {
    match x.kind with
    | Literal x -> yield! x |> withKind env (TokenKind.ofLiteralKind x.kind)
    | VarArg x -> yield! x |> withKind env K.Dot3
    | Function(x1, x2) -> yield! withKind env K.Function x1; yield! funcBody env x2
    | PrefixExp x -> yield! prefixExp env x
    | NewTable x -> yield! tableConstructor env x
    | Binary(x1, x2, x3) -> yield! exp env x1; yield! x2 |> withKind env (TokenKind.ofBinaryOpKind x2.kind); yield! exp env x3
    | Unary(x1, x2) -> yield! x1 |> withKind env (TokenKind.ofUnaryOpKind x1.kind); yield! exp env x2
    }
and expList env { kind = xs } = sepBy (token env K.Comma) (exp env) xs
and funcBody env { kind = FuncBody(x1, x2, x3, x4, x5) } = seq {
    yield! withKind env K.LBracket x1
    yield! option (parameterList env) x2
    yield! withKind env K.RBracket x3
    yield! block env x4
    yield! withKind env K.End x5
    }
and prefixExp env x = seq {
    match x.kind with
    | Apply x -> yield! functionCall env x
    | Var x -> yield! var env x
    | Wrap(x1, x2, x3) ->
        yield! withKind env K.LBracket x1
        yield! exp env x2
        yield! withKind env K.RBracket x3
    }
and tableConstructor env { kind = TableConstructor(x1, x2, x3) } = seq {
    yield! withKind env K.LCBracket x1
    yield! option (fieldList env) x2
    yield! withKind env K.RCBracket x3
    }
and parameterList env x = seq {
    match x.kind with
    | ParameterList(x1, commaAndVarArg) ->
        yield! nameList env x1
        yield! option (tuple2(token env K.Comma, token env K.Dot3)) commaAndVarArg
        // (Token (* `,` *) * Token (* `...` *)) option
    | VarParameter x1 -> yield! withKind env K.Dot3 x1
    }
and functionCall env x = seq {
    match x.kind with
    | Call(x1, x2) -> yield! prefixExp env x1; yield! args env x2
    | CallWithSelf(x1, x2, x3, x4) ->
        yield! prefixExp env x1
        yield! withKind env K.Colon x2
        yield! name env x3
        yield! args env x4
    }
and var env x = seq {
    match x.kind with
    | Variable x -> yield! name env x
    | Index(x1, x2, x3, x4) -> yield! prefixExp env x1; yield! withKind env K.LSBracket x2; yield! exp env x3; yield! withKind env K.RSBracket x4
    | Member(x1, x2, x3) -> yield! prefixExp env x1; yield! withKind env K.Dot x2; yield! name env x3
    }
and fieldSep env x = withKind env (TokenKind.ofFieldSepKind x.kind) x
and fieldList env (FieldList(x1, x2)) = seq {
    yield! sepBy (fieldSep env) (field env) x1
    match x2 with
    | None -> ()
    | Some x2 -> yield! fieldSep env x2
    }
and field env x = seq {
    match x.kind with
    | IndexInit(x1, x2, x3, x4, x5) ->
        yield! withKind env K.LSBracket x1
        yield! exp env x2
        yield! withKind env K.RSBracket x3
        yield! withKind env K.Assign x4
        yield! exp env x5

    | MemberInit(x1, x2, x3) -> yield! name env x1; yield! withKind env K.Assign x2; yield! exp env x3
    | Init x -> yield! exp env x
    }
and nameList env { kind = xs } = sepBy (token env K.Comma) (name env) xs
and args env x = seq {
    match x.kind with
    | Args(x1, x2, x3) -> yield! withKind env K.LBracket x1; yield! option (expList env) x2; yield! withKind env K.RBracket x3
    | TableArg x -> yield! tableConstructor env x
    | StringArg(StringLiteral x) -> yield! withKind env (K.String x.kind) x
    }
and stat env x = seq {
    match x.kind with
    | Assign(x1, x2, x3) -> yield! varList env x1; yield! withKind env K.Assign x2; yield! expList env x3
    | FunctionCall x -> yield! functionCall env x
    | Do(x1, x2, x3) -> yield! withKind env K.Do x1; yield! block env x2; yield! withKind env K.End x3
    | While(x1, x2, x3, x4, x5) -> yield! withKind env K.While x1; yield! exp env x2; yield! withKind env K.Do x3; yield! block env x4; yield! withKind env K.End x5
    | RepeatUntil(x1, x2, x3, x4) -> yield! withKind env K.Repeat x1; yield! block env x2; yield! withKind env K.Until x3; yield! exp env x4
    | If(x1, x2, x3, x4, x5, x6, x7) ->
        yield! withKind env K.If x1
        yield! exp env x2
        yield! withKind env K.Then x3
        yield! block env x4
        for x5 in x5 do yield! elseIfClause env x5
        yield! option (elseClause env) x6
        yield! withKind env K.End x7

    | For(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) ->
        yield! withKind env K.For x1
        yield! name env x2
        yield! withKind env K.Assign x3
        yield! exp env x4
        yield! withKind env K.Comma x5
        yield! exp env x6
        yield! option (tuple2(token env K.Comma, exp env)) x7
        yield! withKind env K.Do x8
        yield! block env x9
        yield! withKind env K.End x10

    | ForIn(x1, x2, x3, x4, x5, x6, x7) ->
        yield! withKind env K.For x1
        yield! nameList env x2
        yield! withKind env K.In x3
        yield! expList env x4
        yield! withKind env K.Do x5
        yield! block env x6
        yield! withKind env K.End x7

    | FunctionDecl(x1, x2, x3) ->
        yield! withKind env K.Function x1
        yield! funcName env x2
        yield! funcBody env x3

    | LocalFunction(x1, x2, x3, x4) ->
        yield! withKind env K.Local x1
        yield! withKind env K.Function x2
        yield! name env x3
        yield! funcBody env x4

    | Local(x1, x2, x3) ->
        yield! withKind env K.Local x1
        yield! nameList env x2
        yield! option (tuple2(token env K.Assign, expList env)) x3
    }

and varList env { kind = xs } = sepBy (token env K.Comma) (var env) xs
and elseIfClause env { kind = ElseIf(x1, x2, x3, x4) } = seq {
    yield! withKind env K.ElseIf x1
    yield! exp env x2
    yield! withKind env K.Then x3
    yield! block env x4
    }
and elseClause env { kind = Else(x1, x2) } = seq {
    yield! withKind env K.Else x1
    yield! block env x2
    }
and funcName env { kind = FuncName(x1, x2, x3) } = seq {
    yield! name env x1
    for dot, n in x2 do
        yield! withKind env K.Dot dot
        yield! name env n
    yield! option (tuple2(token env K.Colon, name env)) x3
    }
and lastStat env x = seq {
    match x.kind with
    | Break x -> yield! withKind env K.Break x
    | Return(x1, x2) -> yield! withKind env K.Return x1; yield! option (expList env) x2
    }
and blockStat env (s, sep) = seq {
    yield! stat env s
    yield! option (token env K.Semicolon) sep
    }
and blockLastStat env (s, sep) = seq {
    yield! lastStat env s
    yield! option (token env K.Semicolon) sep
    }
and block env { kind = x } = seq {
    match x.stats with
    | [] -> ()
    | s::xs ->
        yield! blockStat env s
        for s in xs do
            "\n"
            yield! blockStat env s

    match x.lastStat with
    | None -> ()
    | Some s ->
        match x.stats with
        | [] -> yield! blockLastStat env s
        | _ ->
            "\n"
            yield! blockLastStat env s
    }
