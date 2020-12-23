module LuaChecker.Syntax.DocumentPrinter
open LuaChecker
open LuaChecker.Primitives
open LuaChecker.Syntax
open LuaChecker.Syntax.Documents
open LuaChecker.Syntaxes
open System


type DocumentStyle =
    | LineDocument
    | LongDocument of quoteCount: int
    | LongDocuments of quoteCount: int

type EscapeLevel =
    | Min
    | Control
    | Max

type Options = {
    style: DocumentStyle
    lastNewLine: bool
    escape: EscapeLevel
    numberStyle: Printer.NumberStyle
    charEscape: Printer.EscapeLevel
    stringStyle: Printer.StringStyle
    longStringEqCount: int
    wrapResultType: bool
}
module Options =
    let defaultOptions = {
        style = LineDocument
        lastNewLine = false
        escape = Control
        wrapResultType = false

        numberStyle = Printer.NumberStyle.Decimal
        charEscape = Printer.EscapeLevel.Control
        stringStyle = Printer.StringStyle.DoubleQuote
        longStringEqCount = 0
    }

let escape c = seq {
    match c with
    | '&' -> "&amp;"
    | '"' -> "&quot;"
    | '\'' -> "&apos;"
    | '<' -> "&lt;"
    | '>' -> "&gt;"
    | _ -> sprintf "&%d;" <| int c
}
let comment escapeLeadingWhiteSpaces options (Comment { kind = contents }) = seq {
    let mutable i = 0
    while escapeLeadingWhiteSpaces && i < contents.Length && Char.IsWhiteSpace contents.[i] do
        yield! escape contents.[i]
        i <- i + 1

    for i in i..contents.Length-1 do
        let c = contents.[i]
        match c, options.style with
        | _ when Max <= options.escape -> yield! escape c
        | c, _ when Control <= options.escape && Char.IsControl c -> yield! escape c
        | ('@' | '\n' | '&'), _
        | ']', (LongDocument _ | LongDocuments _) -> yield! escape c
        | _ -> string c
}
/// --[[
let longCommentStart eqCount = seq { "--["; for _ in 1..eqCount do "=" done; "[" }
/// ]]
let longCommentEnd eqCount = seq { "]"; for _ in 1..eqCount do "=" done; "]" }

let name (Annotated(Name { kind = n }, _)) = n
let fieldSep (Annotated({ kind = sep }, _)) =
    match sep with
    | Comma -> ", "
    | Semicolon -> "; "

[<RequireQualifiedAccess>]
type Precedence =
    | Min
    /// p: t, a: t
    | MultiType
    /// T: { x: number }
    | ConstrainedType
    /// fun(): a
    | FunctionType
    /// ...E
    | ConstrainedMultiType
    /// T[]
    | ArrayType
    ///<summary>table&lt;T, U&gt;</summary>
    | PrimitiveType
    | Max

module Precedence =
    let Type = Precedence.MultiType

let rec typePrecedence = function
    | WrappedType _ -> Precedence.PrimitiveType
    | FunctionType _ -> Precedence.FunctionType
    | ConstrainedType _ -> Precedence.ConstrainedType
    | ArrayType _ -> Precedence.ArrayType
    | InterfaceType _
    | NamedType _ -> Precedence.PrimitiveType

    // "" => "()"
    // "t," => "(t,)"
    // "p: t," => "(p: t,)"
    | EmptyType _
    | SingleMultiType _ -> Precedence.PrimitiveType
    // ...e
    // ...e: { f: t }
    | VariadicType { kind = VariadicTypeSign(_, _, Some _) } -> Precedence.ConstrainedMultiType
    // ...
    // T...
    | VariadicType { kind = VariadicTypeSign(_, _, None) } -> Precedence.PrimitiveType
    // p1: t1, t2
    // p1: t1, s...e
    | MultiType2 _ -> Precedence.MultiType

let rec typeSignNoWrap options t = seq {
    match t with
    | WrappedType(_, t, _) ->
        "("; yield! typeSignNoWrap options t.kind; ")"

    | ConstrainedType(t, _, c) ->
        yield! typeSign Precedence.ConstrainedType options t.kind
        ": "
        yield! constraints options c

    | ArrayType(t, _, _) ->
        yield! typeSign Precedence.ArrayType options t.kind; "[]"

    | NamedType(n, ts) ->
        name n
        match ts with
        | None -> ()
        | Some(GenericArguments(_, SepBy(t, ts), sep, _)) ->
            "<"
            yield! typeSign Precedence.ConstrainedType options t.kind
            for _, t in ts do
                ", "
                yield! typeSign Precedence.ConstrainedType options t.kind
            match sep with
            | Some _ -> ", "
            | _ -> ()
            ">"

    | InterfaceType fs -> yield! fields options fs
    | FunctionType(_, _, m1, _, _, m2) ->
        "fun("
        match m1 with
        | Some m1 -> yield! parameters options m1
        | _ -> ()
        "): "
        yield! typeSign Precedence.FunctionType options m2.kind

    | EmptyType _ -> "()"
    | SingleMultiType(_, p, _, _) -> "("; yield! parameter options p; ",)"
    | VariadicType v -> yield! varParameter options v
    | MultiType2(p, _, ps) -> yield! parameter options p; ", "; yield! parameters options ps
    }
and typeSignWrap options t = seq {
    "("; yield! typeSignNoWrap options t; ")"
    }
and typeSign minNoWrapPrecedence options t =
    let p = typePrecedence t
    if p < minNoWrapPrecedence
    then typeSignWrap options t
    else typeSignNoWrap options t

and constraints options c = fields options c
and fields options fs = seq {
    let (Fields(_, SepBy(f, fs), sep, _)) = fs.kind
    "{ "
    yield! field options f
    for sep, f in fs do
        fieldSep sep
        yield! field options f

    match sep with
    | None -> ()
    | Some sep -> fieldSep sep
    " }"
    }
and field options { kind = Field(k, _, t) } = seq {
    yield! fieldKey options k
    ": "
    yield! typeSign Precedence.ConstrainedType options t.kind
    }
and fieldKey options (Annotated({ kind = k }, _)) = seq {
    match k with
    | FieldKey.Bool true -> "true"
    | FieldKey.Bool false -> "false"
    | FieldKey.Number x -> Printer.showNumberCore options.numberStyle x
    | FieldKey.String x ->
        if Name.isValid x
        then x
        else
            // `--- … \n`
            // 行ドキュメントに改行を含めることはできないのでエスケープする
            let charEscape = max options.charEscape Printer.EscapeLevel.Control

            let longStringEqCount = max 0 options.longStringEqCount
            let longStringEqCount =
                match options.style with

                // `--[[ --- … --[[ … ]] … ]]` のように長ドキュメントに、対応するレベルの `]]` を含めることはできないので
                // `--[[ --- … --[=[ … ]=] … ]]` のように `=` の数を変えて対応する
                | LongDocument n
                | LongDocuments n -> if n = longStringEqCount then n + 1 else longStringEqCount

                | LineDocument -> longStringEqCount

            let stringStyle =
                match options.style, options.stringStyle with

                // `--[[ --- … --[=[ ]] ]=] … ]]` のように長コメント内の長文字列の文字はエスケープできないので
                // `--[[ --- … " \93\93 " … ]]` のように文字列形式を変えて対応する
                | (LongDocument _ | LongDocuments _), Printer.StringStyle.LongString
                    when x.Contains "]" || x.Contains "\n" ->
                    Printer.DoubleQuote

                // `--- … --[[⏎]] …` のように行コメント内の長文字列の改行はエスケープできないので
                // `--- … "\10" …` のように文字列形式を変えて対応する
                | _, Printer.StringStyle.LongString when x.Contains "\n" ->
                    Printer.DoubleQuote

                | _ -> options.stringStyle

            let requireEscape struct(x, i) =
                Printer.isRequireEscape stringStyle charEscape (x, i) ||

                match options.style with
                | LongDocument _
                | LongDocuments _ -> x.[i] = ']'
                | LineDocument -> false

            yield! Printer.showStringCore stringStyle longStringEqCount requireEscape x
    }
and parameters options ps = seq {
    match ps with
    | Parameters(SepBy(p, ps)) ->
        yield! parameter options p
        for _, p in ps do
            ", "
            yield! parameter options p
    }
and parameters0 options xs = seq {
    "("; yield! typeSignNoWrap options xs; ")"
    }
and results options { kind = xs } = seq {
    match xs with
    | EmptyType _ -> "()"
    | MultiType2 _ ->
        if options.wrapResultType
        then yield! parameters0 options xs
        else yield! typeSignNoWrap options xs
    | _ -> yield! typeSign Precedence.Type options xs
    }
and parameter options { kind = Parameter(n, t) } = seq {
    match n with
    | None ->
        match t.kind with
        | ConstrainedType _ -> yield! typeSignWrap options t.kind
        | _-> yield! typeSign Precedence.FunctionType options t.kind
    | Some(n, _) ->
        name n
        ": "
        yield! typeSign Precedence.ConstrainedType options t.kind
    }
and varParameter options { kind = VariadicTypeSign(n, _, e) } = seq {
    match n with
    | None -> ()
    | Some n -> name n
    "..."
    match e with
    | None -> ()
    | Some t -> yield! typeSign Precedence.PrimitiveType options t.kind
    }

let visibility = function
    | Visibility.Public -> "public"
    | Visibility.Protected -> "protected"
    | Visibility.Private -> "private"

let typeParameter options x = seq {
    match x.kind with
    | TypeParameter(n, None) -> name n
    | TypeParameter(n, Some(_, c)) -> name n; ": "; yield! constraints options c
    | VariadicTypeParameter(n, _, None) -> name n; "..."
    | VariadicTypeParameter(n, _, Some c) -> name n; "..."; yield! typeSign Precedence.ConstrainedType options c.kind
}
let tagTail options a = seq {
    match a.kind with
    | UnknownTag(n, c) -> name n; " "; yield! comment true options c
    | TypeTag(_, t) -> "type "; yield! typeSign Precedence.Type options t.kind
    | GlobalTag(_, n, t) -> "global "; name n; " "; yield! typeSign Precedence.Type options t.kind
    | FeatureTag(_, n) -> "_Feature "; name n;
    | ClassTag(_, n, parent) ->
        "class "; name n;
        match parent with
        | Some(_, t) -> " : "; yield! typeSign Precedence.Type options t.kind
        | _ -> ()

    | FieldTag(_, v, n, t) ->
        "field "
        match v with
        | Some(Annotated(v, _)) -> visibility v.kind; " "
        | _ -> ()
        yield! fieldKey options n; " ";
        yield! typeSign Precedence.Type options t.kind

    | GenericTag(_, SepBy(p, ps)) ->
        "generic "
        yield! typeParameter options p
        for _, p in ps do
            ", "
            yield! typeParameter options p
}
let tag options { kind = Tag(_, t) } = seq {
    "@"; yield! tagTail options t
}
/// --- summary tag …
let documentAsLineComment options { kind = Document(summary, ts) } = seq {
    "---"
    yield! comment false options summary
    for a in ts do
        yield! tag options a
}
/// `--- …` or `--[[ --- … ]]`
let document options d = seq {
    match options.style with
    | LineDocument
    | LongDocument _ -> yield! documentAsLineComment options d
    | LongDocuments eqCount ->
        let eqCount = max 0 eqCount
        yield! longCommentStart eqCount
        yield! documentAsLineComment options d

        let (Document(_, tags)) = d.kind
        match List.tryLast tags with
        | Some { kind = Tag(_, { kind = TypeTag(_, { kind = ArrayType _ }) }) } ->
            // `--[[ ---@type …[]]]` -> `--[[ ---@type …[] ]]`
            " "

        | _ -> ()

        yield! longCommentEnd eqCount
}
/// `--- …⏎--- …` or `--[[ --- … ]]⏎--[[ --- … ]]`
let documents options ds = seq {
    yield! Seq.map (document options) ds |> Seq.sepBy ["\n"]
    if options.lastNewLine then "\n"
}
let allDocuments options ds = seq {
    match options.style with
    | LineDocument
    | LongDocuments _ -> yield! documents options ds
    | LongDocument eqCount ->
        let eqCount = max 0 eqCount
        yield! longCommentStart eqCount; "\n"
        yield! documents options ds; "\n"
        yield! longCommentEnd eqCount
}
