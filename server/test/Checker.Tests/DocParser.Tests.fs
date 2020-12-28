module LuaChecker.Parser.Document.Tests
open FsCheck
open LuaChecker
open LuaChecker.Checker.Test.Utils
open LuaChecker.Primitives
open LuaChecker.Syntax.DocumentPrinter
open LuaChecker.Syntax.Documents
open LuaChecker.Syntax
open LuaChecker.Test
open Xunit


type RoundTripConfig = {
    leadingNoise: string NonNull
    trailingNoise: string NonNull
    options: DocumentPrinter.Options
}
module Printer =
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

[<AutoOpen>]
module private Helpers =
    module SepBy =
        let inline map mapping x = SepBy.mapSep (fun x -> x) mapping x
        let cons x sep (SepBy(x1, xs)) = SepBy(x, (sep, x1)::xs)

    let parseCore source position length =
        let s = Scanner.create source
        Parser.DocumentParser.documents s position length

    let parseRange source position length =
        match parseCore source position length with
        | xs, [] -> xs
        | xs, es -> failwithf "%A, %A" es xs

    let parse source = parseRange source 0 source.Length

    let print options ds = Printer.allDocuments options ds |> String.concat ""

    module Mapping =
        let source (mapSpan, _) t = { kind = t.kind; trivia = mapSpan t.trivia }
        let annotated f (Annotated(t, a)) = Annotated(f t, a)
        let identifier (_, mapTrivia) t = annotated (Name.map mapTrivia) t
        let reserved (mapSpan, _) t = annotated (fun t -> { kind = t.kind; trivia = mapSpan t.trivia }) t
        let inline sourced (mapSpan, _) x mapKind = { kind = mapKind x.kind; trivia = mapSpan x.trivia }
        let tuple2 (f1, f2) (x1, x2) = f1 x1, f2 x2

        let comment f (Comment x) = source f x |> Comment
        let fieldKey f x = source f x

        let rec typeSign f x = sourced f x <| function
            | WrappedType(l, t, r) -> WrappedType(reserved f l, typeSign f t, reserved f r)
            | InterfaceType fs -> InterfaceType <| fields f fs
            | ArrayType(t, l, r) -> ArrayType(typeSign f t, reserved f l, reserved f r)
            | ConstrainedType(t, s, c) -> ConstrainedType(typeSign f t, reserved f s, constraints f c)
            | FunctionType(t, l, m1, r, colon, m2) ->
                FunctionType(reserved f t, reserved f l, Option.map (parameters f) m1, reserved f r, reserved f colon, typeSign f m2)

            | NamedType(n, ts) -> NamedType(identifier f n, Option.map (genericArguments f) ts)

            // multi type
            | EmptyType(l, r) -> EmptyType(reserved f l, reserved f r)
            | MultiType2(p, c, ps) -> MultiType2(parameter f p, reserved f c, parameters f ps)
            | VariadicType v -> variadicTypeSign f v |> VariadicType
            | SingleMultiType(l, t, s, r) -> SingleMultiType(reserved f l, parameter f t, reserved f s, reserved f r)

        and variadicTypeSign f x = sourced f x <| fun (VariadicTypeSign(n, dot3, c)) ->
            VariadicTypeSign(Option.map (identifier f) n, reserved f dot3, Option.map (typeSign f) c)

        and genericArguments f (GenericArguments(l, ts, s, r)) =
            GenericArguments(reserved f l, SepBy.mapSep (reserved f) (typeSign f) ts, Option.map (reserved f) s, reserved f r)

        and parameters f (Parameters ps) = SepBy.mapSep (reserved f) (parameter f ) ps |> Parameters

        and constraints f x = fields f x

        and fields f x = sourced f x <| fun (Fields(l, fs, s, r)) ->
            Fields(reserved f l, SepBy.mapSep (reserved f) (field f) fs, Option.map (reserved f) s, reserved f r)

        and field f x = sourced f x <| fun (Field(k, c, t)) ->
            Field(annotated (fieldKey f) k, reserved f c, typeSign f t)

        and parameter f x = sourced f x <| fun (Parameter(n, t)) ->
            Parameter(Option.map (tuple2 (identifier f, reserved f)) n, typeSign f t)

        let typeParameter f x = sourced f x <| function
            | TypeParameter(n, c) -> TypeParameter(identifier f n, Option.map (tuple2 (reserved f, constraints f)) c)
            | VariadicTypeParameter(n, dot3, c) -> VariadicTypeParameter(identifier f n, reserved f dot3, Option.map (typeSign f) c)

        let tagTail f x = sourced f x <| function
            | UnknownTag(a, c) -> UnknownTag(identifier f a, comment f c)
            | TypeTag(a, t) -> TypeTag(reserved f a, typeSign f t)
            | GlobalTag(a, n, t) -> GlobalTag(reserved f a, identifier f n, typeSign f t)
            | FeatureTag(a, n) -> FeatureTag(reserved f a, identifier f n)
            | ClassTag(a, n, t) -> ClassTag(reserved f a, identifier f n, Option.map (tuple2(reserved f, typeSign f)) t)
            | FieldTag(a, v, n, t) -> FieldTag(reserved f a, Option.map (annotated (source f)) v, annotated (fieldKey f) n, typeSign f t)
            | GenericTag(a, ps) -> GenericTag(reserved f a, SepBy.mapSep (reserved f) (typeParameter f) ps)

        let tag f x = sourced f x <| fun (Tag(at, tail)) ->
            Tag(reserved f at, tagTail f tail)

        let document f x = sourced f x <| fun (Document(c, xs)) ->
            Document(comment f c, List.map (tag f) xs)

    let normalize ds =
        List.map (Mapping.document ((fun _ -> Span.empty), (fun _ -> Trivia.createEmpty()))) ds

    let withEmptyTrivia k = { kind = k; trivia = Trivia.createEmpty() }
    let withEmptySpan k = { kind = k; trivia = Span.empty }
    let withEmptyAnnotation k = Annotated(k, HEmpty)
    /// withEmptySpan >> withEmptyAnnotation
    let withEmpty k = withEmptySpan k |> withEmptyAnnotation
    let insert sep (x, xs) = SepBy(x, [for x in xs -> sep, x])

    let comment x = x |> withEmptySpan |> Comment
    let printConfig = {
        leadingNoise = NonNull ""
        trailingNoise = NonNull ""
        options = Options.defaultOptions
    }
    let name n = n |> withEmptyTrivia |> Name |> withEmptyAnnotation
    let document c ans = Document(comment c, ans) |> withEmptySpan
    let reserved = HEmpty |> withEmpty
    let fieldSep = Comma |> withEmpty
    let fields = function
        | [] -> failwithf "empty list"
        | x::xs ->

        let fs =
            insert fieldSep (x, xs)
            |> SepBy.map (fun (k, t) ->
                Field(k |> withEmpty, reserved, t)
                |> withEmptySpan
            )
        Fields(reserved, fs, None, reserved)
        |> withEmptySpan

    let toStringKey = List.map (fun (k, t) -> FieldKey.String k, t)
    let stringFields = toStringKey >> fields

    let type0 n = NamedType(name n, None) |> withEmptySpan
    let namedType n xs =
        match xs with
        | [] -> type0 n
        | x::xs ->

        let ts = GenericArguments(reserved, insert reserved (x, xs), None, reserved)
        NamedType(name n, Some ts) |> withEmptySpan

    let interfaceType = fields >> InterfaceType >> withEmptySpan
    let stringInterfaceType = toStringKey >> interfaceType

    let multiTypeCore ts v =
        match ts, v with
        | [], None -> EmptyType(reserved, reserved)
        | [], Some v -> VariadicType v
        | [p], None -> SingleMultiType(reserved, p, reserved, reserved)
        | p::ps, v ->
            let v = v |> Option.map (fun v -> Parameter(None, VariadicType v |> withEmptySpan) |> withEmptySpan)
            MultiType2(p, reserved, Parameters(insert reserved (p, ps @ Option.toList v)))
        |> withEmptySpan

    let multiType ts = multiTypeCore ts None
    /// ts, v
    let multiTypeV ts v = multiTypeCore ts (Some v)
    /// t[]
    let arrayType t = ArrayType(t, reserved, reserved) |> withEmptySpan
    /// (t)
    let wrappedType t = WrappedType(reserved, t, reserved) |> withEmptySpan
    /// fun(ts1, v1): ts2, v2
    let functionTypeCore (ts1, v1) (ts2, v2) =
        let m1 =
            let m1 = multiTypeCore ts1 v1
            match m1.kind with
            | EmptyType _ -> None
            | VariadicType _ -> Some(Parameters(SepBy(Parameter(None, m1) |> withEmptySpan, [])))
            | SingleMultiType(_, p, _, _) -> Some(Parameters(SepBy(p, [])))
            | MultiType2(p1, _, Parameters ps) -> Some(Parameters(SepBy.cons p1 reserved ps))
            | _ -> failwith ""

        let m2 = multiTypeCore ts2 v2
        FunctionType(reserved, reserved, m1, reserved, reserved, m2) |> withEmptySpan

    /// fun(ts1): ts2
    let functionType ts1 ts2 = functionTypeCore (ts1, None) (ts2, None)
    /// name...: elemType
    let varParamCore name elemType = VariadicTypeSign(name, reserved, elemType) |> withEmptySpan
    /// ...: elemType
    let varParamE elemType = varParamCore None (Some elemType)
    /// ...
    let varParam = varParamCore None None
    let param t = Parameter(None, t) |> withEmptySpan
    let paramN n t = Parameter(Some(name n, reserved), t) |> withEmptySpan

    let tag tail = Tag(reserved, tail) |> withEmptySpan

    let typeTag t = TypeTag(reserved, t) |> withEmptySpan |> tag
    let genericTag = function
        | [] -> failwithf "empty list"
        | x::xs -> GenericTag(reserved, insert reserved (x, xs)) |> withEmptySpan |> tag

    let typeParameterFs n fs = TypeParameter(name n, Some(reserved, fs)) |> withEmptySpan
    let constrainedType t c = ConstrainedType(t, reserved, c) |> withEmptySpan

let [<Fact(DisplayName = "---@a")>] simpleDocComment() =
    parse "---@a" =? [
        {
            kind =
                Document(
                    Comment {
                        kind = ""
                        trivia = { start = 3; end' = 3 }
                    },
                    [
                        {
                            kind =
                                Tag(
                                    Annotated({
                                        kind = HEmpty
                                        trivia = { start = 3; end' = 4 }
                                    }, HEmpty),
                                    {
                                        kind =
                                            UnknownTag(
                                                Annotated(Name {
                                                    kind = "a"
                                                    trivia = {
                                                        leadingTriviaLength = 0
                                                        span = { start = 4; end' = 5 }
                                                        trailingTriviaLength = 0
                                                        leadingDocument = None
                                                        trailingDocument = None
                                                    }
                                                }, HEmpty),
                                                Comment {
                                                    kind = ""
                                                    trivia = { start = 5; end' = 5 }
                                                }
                                            )
                                        trivia = { start = 4; end' = 5 }
                                    }
                                )
                            trivia = { start = 3; end' = 5 }
                        }
                    ]
                )
            trivia = { start = 3; end' = 5 }
        }
    ]

let [<Fact(DisplayName = "---a⏎--b⏎---c")>] docCommentAndNormalLineComment() =
    parse "---a\n--b\n---c"
    |> normalize =? [
        document "a" []
        document "c" []
    ]

let [<Fact(DisplayName = "---a⏎--[[b]]⏎---c")>] docCommentAndNormalLongComment() =
    parse "---a\n--[[b]]\n---c"
    |> normalize =? [
        document "a" []
        document "c" []
    ]

let roundTripTest { trailingNoise = NonNull n1; leadingNoise = NonNull n2; options = options } expected =
    let expectedSource = print options expected
    let expectedSourceWithNoise = n2 + expectedSource + n1
    let actual = parseRange expectedSourceWithNoise n2.Length expectedSource.Length
    let actualSource = print options actual
    equalsWithMessage (normalize actual, normalize expected) $"{nameof expectedSourceWithNoise} = `{expectedSourceWithNoise}`, {nameof actualSource} = `{actualSource}`"

let typeSignRoundTripTest expected =
    roundTripTest printConfig [document "" [typeTag expected]]

let [<Fact>] docCommentRoundTrip() = checkWith (fun c -> { c with MaxTest = c.MaxTest * 2 }) roundTripTest

let [<Fact(DisplayName = "--[[ ]]")>] emptyLongComment() =
    []
    |> roundTripTest {
        printConfig with
            options = {
                printConfig.options with
                    style = LongDocument 0
            }
    }

let [<Fact(DisplayName = "---a")>] summaryOnly() =
    [
        document "a" []
    ]
    |> roundTripTest printConfig

let [<Fact(DisplayName = "---⏎---⏎")>] emptyLineDocument2() =
    [
        document "" []
        document "" []
    ]
    |> roundTripTest printConfig

let [<Fact(DisplayName = "a---")>] emptyLineDocumentWithNoise() =
    [
        document "" []
    ]
    |> roundTripTest {
        printConfig with
            leadingNoise = NonNull "a"
    }

let [<Fact(DisplayName = "---a⏎---⏎")>] lineDocument2() =
    [
        document "a" []
        document "" []
    ]
    |> roundTripTest printConfig

let [<Fact(DisplayName = "--[[---]]")>] emptySingleDocInLongDoc() =
    [
        document "" []
    ]
    |> roundTripTest {
        printConfig with
            options = {
                printConfig.options with
                    style = LongDocuments 0
                    lastNewLine = true
            }
    }

let [<Fact(DisplayName = "---&amp;")>] escapedCommentAmp() =
    [
        document "&" []
    ]
    |> roundTripTest printConfig

let [<Fact(DisplayName = "--[[⏎---a⏎---⏎]]")>] lineDoc2InLongDoc() =
    [
        document "a" []
        document "" []
    ]
    |> roundTripTest {
        printConfig with
            options = {
                printConfig.options with
                    style = LongDocument 0
            }
    }

let [<Fact(DisplayName = "---@a &12;")>] commentEscape() =
    [
        document "" [
            UnknownTag(name "a", comment "\f") |> withEmptySpan |> tag
        ]
    ]
    |> roundTripTest {
        printConfig with
            options = {
                printConfig.options with
                    escape = Min
            }
    }

let [<Fact(DisplayName = "---@type a@type a")>] type2() =
    [
        document "" [
            typeTag(type0 "a")
            typeTag(type0 "a")
        ]
    ]
    |> roundTripTest printConfig

let [<Fact(DisplayName = "--[[---@type { [=[]=]: a }]]")>] longStringInLongDocument() =
    [
        document "" [
            typeTag(stringInterfaceType [
                "", type0 "a"
            ])
        ]
    ]
    |> roundTripTest {
        printConfig with
            options = {
                printConfig.options with
                    style = LongDocuments 0
                    stringStyle = Printer.LongString
            }
    }

let [<Fact(DisplayName = "--[=[---@type { \"\\93=\\93\": a }]=]")>] longDocumentStringKeyEscape() =
    [
        document "" [
            typeTag(stringInterfaceType [
                "]=]", type0 "a"
            ])
        ]
    ]
    |> roundTripTest {
        printConfig with
            options = {
                printConfig.options with
                    style = LongDocuments 1
                    longStringEqCount = 1
                    stringStyle = Printer.LongString
            }
    }

let [<Fact(DisplayName = "--[=[--- &93;=&93; ]=]")>] longDocumentCommentEscape() =
    [
        document "]=]" []
    ]
    |> roundTripTest {
        printConfig with
            options = {
                printConfig.options with
                    style = LongDocuments 1
            }
    }

let [<Fact(DisplayName = "--[[---@field --[=[]=] a]]")>] longStringInNegativeEqCountInLongDocument() =
    [
        document "" [
            FieldTag(
                reserved,
                None,
                FieldKey.String "" |> withEmpty,
                type0 "a"
            )
            |> withEmptySpan
            |> tag
        ]
    ]
    |> roundTripTest {
        printConfig with
            options = {
                printConfig.options with
                    style = LongDocuments 0
                    stringStyle = Printer.LongString
                    longStringEqCount = -1
            }
    }

let [<Fact(DisplayName = "---@generic a: { f: x }")>] genericWithInterfaceConstraints() =
    [
        document "" [
            genericTag [
                typeParameterFs "a" (stringFields ["f", type0 "x"])
            ]
        ]
    ]
    |> roundTripTest printConfig

let [<Fact(DisplayName = "---@type { \"\\10\": a }")>] newLineInLongStringInTypeTag() =
    [
        document "" [
            typeTag(stringInterfaceType [
                "\n", type0 "a"
            ])
        ]
    ]
    |> roundTripTest {
        printConfig with
            options = {
                printConfig.options with
                    stringStyle = Printer.LongString
            }
    }

let [<Fact(DisplayName = "--[[---@type a[] ]]")>] arrayTypeInLongDocument() =
    [
        document "" [
            typeTag(arrayType (type0 "a"))
        ]
    ]
    |> roundTripTest {
        printConfig with
            options =
            { printConfig.options with
                style = LongDocuments 0
                lastNewLine = true
            }
    }

let [<Fact(DisplayName = "---@a a")>] unknownTag() =
    [
        document "" [
            Tag(reserved, UnknownTag(name "a", "a" |> withEmptySpan |> Comment) |> withEmptySpan)
            |> withEmptySpan
        ]
    ]
    |> roundTripTest printConfig

let [<Fact(DisplayName = "---@field public x a")>] visibility() =
    [
        document "" [
            FieldTag(
                reserved,
                Visibility.Public |> withEmpty |> Some,
                FieldKey.String "x" |> withEmpty,
                type0 "a"
            )
            |> withEmptySpan
            |> tag
        ]
    ]
    |> roundTripTest printConfig

let [<Fact>] typeSignRoundTrip() = checkWith (fun c -> { c with MaxTest = c.MaxTest * 2 }) typeSignRoundTripTest

let [<Fact(DisplayName = "---@type a")>] simpleTypeTag() =
    type0 "a"
    |> typeSignRoundTripTest

let [<Fact(DisplayName = "---@type { -1: a }")>] negativeFieldKey() =
    interfaceType [
        FieldKey.Number -1., type0 "a"
    ]
    |> typeSignRoundTripTest

let [<Fact(DisplayName = "---@type { a: b }")>] nameKey() =
    stringInterfaceType [
        "a", type0 "b"
    ]
    |> typeSignRoundTripTest

let [<Fact(DisplayName = "---@type (fun(): ...a)[]")>] funTypeConstrainedVarResultInArrayType() =
    arrayType (wrappedType (functionTypeCore ([], None) ([], Some(varParamE (type0 "a")))))
    |> typeSignRoundTripTest

let [<Fact(DisplayName = "---@type { \"\\n\": a }")>] nInterfaceType() =
    stringInterfaceType [
        "\n", type0 "a"
    ]
    |> typeSignRoundTripTest

let [<Fact(DisplayName = "---@type { \"a\\n\": a }")>] aAndNewLineInField() =
    stringInterfaceType [
        "a\n", type0 "a"
    ]
    |> typeSignRoundTripTest

let [<Fact(DisplayName = "---@global a a")>] simpleGlobal() =
    [
        document "" [
            GlobalTag(reserved, name "a", type0 "a") |> withEmptySpan |> tag
        ]
    ]
    |> roundTripTest printConfig

let [<Fact(DisplayName = "---@type ()")>] emptyType() =
    multiType []
    |> typeSignRoundTripTest

let [<Fact(DisplayName = "---@type (a,)")>] multi1Type() =
    multiType [param <| type0 "a"]
    |> typeSignRoundTripTest

let [<Fact(DisplayName = "---@type ...a")>] varParameterWithConstraint() =
    multiTypeV [] (varParamE(type0 "a"))
    |> typeSignRoundTripTest

let [<Fact(DisplayName = "---@type a<x, y>")>] genericType2() =
    namedType "a" [type0 "x"; type0 "y"]
    |> typeSignRoundTripTest

let [<Fact(DisplayName = "---@type a<(x, y)>")>] multiType2InGeneric1() =
    wrappedType (multiType [param <| type0 "x"; param <| type0 "y"])
    |> typeSignRoundTripTest

let [<Fact(DisplayName = "---@type ...")>] multiTypeVar() =
    multiTypeV [] varParam
    |> typeSignRoundTripTest

let [<Fact(DisplayName = "---@type (p: t, ...)")>] withParameterName() =
    wrappedType (multiTypeV [paramN "p" <| type0 "t"] varParam)
    |> typeSignRoundTripTest

let [<Fact(DisplayName = "---@type fun(a): ()")>] emptyResultFunctionType() =
    functionType [param(type0 "a")] []
    |> typeSignRoundTripTest

let [<Fact(DisplayName = "---@type { f1: t1, f2: t2 }")>] interfaceType2() =
    stringInterfaceType [
        "f1", type0 "t1"
        "f2", type0 "t2"
    ]
    |> typeSignRoundTripTest

let [<Fact(DisplayName = "---@type { f: a, }")>] singleInterfaceType() =
    InterfaceType(
        Fields(
            reserved,
            SepBy(Field(FieldKey.String "f" |> withEmpty, reserved, type0 "a") |> withEmptySpan, []),
            Some(Comma |> withEmpty),
            reserved
        )
        |> withEmptySpan
    )
    |> withEmptySpan
    |> typeSignRoundTripTest

let [<Fact(DisplayName = "---@type a, a")>] multiType2() =
    MultiType2(
        param (type0 "a"),
        reserved,
        Parameters(SepBy(param (type0 "a"), []))
    )
    |> withEmptySpan
    |> typeSignRoundTripTest

let [<Fact(DisplayName = "---@type { f: a; }")>] lastFieldSemicolon() =
    InterfaceType(
        Fields(
            reserved,
            SepBy(Field(FieldKey.String "f" |> withEmpty, reserved, type0 "a") |> withEmptySpan, []),
            Some(Semicolon |> withEmpty),
            reserved
        )
        |> withEmptySpan
    )
    |> withEmptySpan
    |> typeSignRoundTripTest

let [<Fact(DisplayName = "---@type a<x, >")>] genericLastSep() =
    NamedType(
        name "a",
        GenericArguments(
            reserved,
            SepBy(type0 "x", []),
            Some reserved,
            reserved
        )
        |> Some
    )
    |> withEmptySpan
    |> typeSignRoundTripTest

let roundTripTypeSign t =
    [document "" [typeTag t]]
    |> print printConfig.options
    |> parse
    |> normalize
    |> function
    | [{ kind = Document(Comment { kind = "" }, [ { kind = Tag(_, { kind = TypeTag(_, t) }) } ]) }] -> t
    | x -> failwith $"%A{x}"

let [<Fact(DisplayName = "---@type (...a)[]")>] autoWrapVariadicTypeInArrayType() =
    arrayType (wrappedType (multiTypeV [] (varParamE (type0 "a"))))
    |> typeSignRoundTripTest

let [<Fact(DisplayName = "---@type ((x,))")>] genericWrap() =
    wrappedType(multiType [param (type0 "x")])
    |> typeSignRoundTripTest

let [<Fact(DisplayName = "---@type ((), ...)")>] multiTail() =
    wrappedType(multiType [
        param (multiType [])
        param (multiTypeV [] varParam)
    ])
    |> typeSignRoundTripTest

let [<Fact(DisplayName = "---@type (a: { f: x })[]")>] autoWrapConstrainedTypeInArrayType() =
    let innerType = constrainedType (type0 "a") (stringFields ["f", type0 "x"])

    arrayType innerType
    |> roundTripTypeSign =?
        arrayType (wrappedType innerType)

let [<Fact(DisplayName = "---@type ...(a, a)")>] autoWrapMultiTypeInVariadicTypeConstraint() =
    let innerType = multiType [param (type0 "a"); param (type0 "a")]

    multiTypeV [] (varParamE innerType)
    |> roundTripTypeSign =?
        multiTypeV [] (varParamE (wrappedType innerType))

let [<Fact(DisplayName = "---@type fun(): a: { f: x }")>] functionConstrainedType() =
    constrainedType
        (FunctionType(reserved, reserved, None, reserved, reserved, type0 "a") |> withEmptySpan)
        (stringFields ["f", type0 "x"])
    |> typeSignRoundTripTest

let [<Fact(DisplayName = "---@type ((fun(): a),)")>] autoWrapFunctionTypeInSingleMultiType() =
    let innerType = 
        FunctionType(
            reserved,
            reserved,
            None,
            reserved,
            reserved,
            type0 "a"
        )
        |> withEmptySpan

    multiType [param innerType]
    |> typeSignRoundTripTest
