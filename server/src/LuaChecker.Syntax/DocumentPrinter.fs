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
    fieldSeparator: FieldSepKind
    lastFieldSeparator: bool
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
        fieldSeparator = Comma
        lastFieldSeparator = false
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

let name (Name { kind = n }) = n
let fieldSep options =
    match options.fieldSeparator with
    | Comma -> ", "
    | Semicolon -> "; "

[<RequireQualifiedAccess>]
type Precedence =
    | Min
    /// p: t, a: t
    | MultiType
    /// fun(): ()
    | FunctionType
    /// ...E
    | ConstrainedMultiType
    /// T: { x: number }
    | ConstrainedType
    /// T[]
    | ArrayType
    ///<summary>table&lt;T, U&gt;</summary>
    | PrimitiveType
    | Max

module Precedence =
    let Type = Precedence.FunctionType

let typePrecedence = function
    | FunctionType _ -> Precedence.FunctionType
    | ConstrainedType _ -> Precedence.ConstrainedType
    | ArrayType _ -> Precedence.ArrayType
    | InterfaceType _
    | NamedType _ -> Precedence.PrimitiveType

    // "" => "()"
    // "t," => "(t,)"
    // "p: t," => "(p: t,)"
    | MultiType([], None)
    | MultiType([_], None) -> Precedence.Min
    // ...e
    // ...e: { f: t }
    | MultiType([], Some { kind = VariadicParameter(_, Some _) }) -> Precedence.ConstrainedMultiType
    // ...
    // T...
    | MultiType([], Some _) -> Precedence.PrimitiveType
    // p1: t1, t2
    // p1: t1, s...e
    | MultiType _ -> Precedence.MultiType

let rec typeSignNoWrap options t = seq {
    match t.kind with
    | ConstrainedType(t, c) ->
        yield! typeSign Precedence.ConstrainedType options t
        ": "
        yield! constraints options c

    | ArrayType t ->
        yield! typeSign Precedence.ArrayType options t; "[]"

    | NamedType(n, ts) ->
        name n
        match ts with
        | [] -> ()
        | t::ts ->
            "<"
            yield! typeSign Precedence.FunctionType options t
            for t in ts do
                ", "
                yield! typeSign Precedence.FunctionType options t
            ">"

    | InterfaceType fs -> yield! fields options fs
    | FunctionType(m1, m2) ->
        "fun"
        yield! parameters0 options m1
        ": "
        yield! typeSign Precedence.FunctionType options m2

    | MultiType([], None) -> ()
    | MultiType([p], None) -> yield! parameter options p
    | MultiType([], Some v) -> yield! varParameter options v
    | MultiType(p::ps, v) ->
        yield! parameter options p
        for p in ps do
            ", "
            yield! parameter options p
        match v with
        | None -> ()
        | Some v ->
            ", "
            yield! varParameter options v
    }
and typeSignWrap options t = seq {
    "("
    yield! typeSignNoWrap options t
    match t.kind with
    | MultiType([_], None) -> ","
    | _ -> ()
    ")"
    }
and typeSign minNoWrapPrecedence options t =
    let p = typePrecedence t.kind
    if p < minNoWrapPrecedence
    then typeSignWrap options t
    else typeSignNoWrap options t

and constraints options c = fields options c
and fields options fs = seq {
    let (Fields(NonEmptyList(f, fs))) = fs.kind
    "{ "
    yield! field options f
    for f in fs do
        fieldSep options
        yield! field options f

    if options.lastFieldSeparator then
        fieldSep options
    " }"
    }
and field options { kind = Field(k, t) } = seq {
    yield! fieldKey options k
    ": "
    yield! typeSign Precedence.FunctionType options t
    }
and fieldKey options { kind = k } = seq {
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
and parameters0 options xs = seq {
    "("; yield! typeSignNoWrap options xs; ")"
    }
and results options xs = seq {
    match xs.kind with
    | MultiType([], None) -> "()"
    | MultiType _ ->
        if options.wrapResultType
        then yield! parameters0 options xs
        else yield! typeSignNoWrap options xs
    | _ -> yield! typeSign Precedence.Type options xs
    }
and parameter options { kind = Parameter(n, t) } = seq {
    match n with
    | None ->
        match t.kind with
        | ConstrainedType _ -> yield! typeSignWrap options t
        | _-> yield! typeSign Precedence.ArrayType options t
    | Some n ->
        name n
        ": "
        yield! typeSign Precedence.Type options t
    }
and varParameter options { kind = VariadicParameter(n, e) } = seq {
    match n with
    | None -> ()
    | Some n -> name n
    "..."
    match e with
    | None -> ()
    | Some t -> yield! typeSign Precedence.Type options t
    }

let visibility = function
    | Visibility.Public -> "public"
    | Visibility.Protected -> "protected"
    | Visibility.Private -> "private"

let typeParameter options x = seq {
    match x.kind with
    | TypeParameter(n, None) -> name n
    | TypeParameter(n, Some c) -> name n; ": "; yield! constraints options c
    | VariadicTypeParameter(n, None) -> name n; "..."
    | VariadicTypeParameter(n, Some c) -> name n; "..."; yield! typeSign Precedence.ConstrainedType options c
}
let tag options a = seq {
    match a.kind with
    | UnknownTag(n, c) -> "@"; name n; " "; yield! comment true options c
    | TypeTag t -> "@type "; yield! typeSign Precedence.Type options t
    | GlobalTag(n, t) -> "@global "; name n; " "; yield! typeSign Precedence.Type options t
    | FeatureTag n -> "@_Feature "; name n;
    | ClassTag(n, parent) ->
        "@class "; name n;
        match parent with
        | Some t -> " : "; yield! typeSign Precedence.Type options t
        | _ -> ()

    | FieldTag(v, n, t) ->
        "@field "
        match v with
        | Some v -> visibility v; " "
        | _ -> ()
        yield! fieldKey options n; " ";
        yield! typeSign Precedence.Type options t

    | GenericTag(NonEmptyList(p, ps)) ->
        "@generic "
        yield! typeParameter options p
        for p in ps do
            ", "
            yield! typeParameter options p
}
/// --- summary tag …
let documentAsLineComment options { kind = Document(summary, ts) } = seq {
    "---"; yield! comment false options summary; for a in ts do yield! tag options a
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
        | Some { kind = TypeTag { kind = ArrayType _ } } ->
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
