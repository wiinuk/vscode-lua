module LuaChecker.Parser.Document.Tests
open FsCheck
open LuaChecker
open LuaChecker.Checker.Test.Utils
open LuaChecker.Primitives
open LuaChecker.Syntax.DocumentPrinter
open LuaChecker.Syntax.Documents
open LuaChecker.Syntax
open Xunit


type RoundTripConfig = {
    leadingNoise: string NonNull
    trailingNoise: string NonNull
    options: DocumentPrinter.Options
}
[<AutoOpen>]
module private Helpers =
    let equalsWithMessage (l, r) format =
        Printf.ksprintf (fun message ->
            if not (l = r) then failwithf "%A =? %A\nmessage: %s" l r message
        ) format

    let parseCore source position length =
        let s = Scanner.create source
        Parser.DocumentParser.documents s position length

    let parseRange source position length =
        match parseCore source position length with
        | xs, [] -> xs
        | xs, es -> failwithf "%A, %A" es xs

    let parse source = parseRange source 0 source.Length

    let print options ds = allDocuments options ds |> String.concat ""

    module Mapping =
        let source (mapSpan, _) t = { kind = t.kind; trivia = mapSpan t.trivia }
        let name (_, mapTrivia) t = Name.map mapTrivia t
        let inline sourced (mapSpan, _) x mapKind = { kind = mapKind x.kind; trivia = mapSpan x.trivia }

        let comment f (Comment x) = source f x |> Comment
        let fieldKey f x = source f x

        let rec typeSign f x = sourced f x <| function
            | InterfaceType fs -> InterfaceType <| fields f fs
            | ArrayType t -> ArrayType <| typeSign f t
            | ConstrainedType(t, c) -> ConstrainedType(typeSign f t, constraints f c)
            | FunctionType(m1, m2) -> FunctionType(typeSign f m1, typeSign f m2)
            | NamedType(n, ts) -> NamedType(name f n, List.map (typeSign f) ts)
            | MultiType(ps, v) -> MultiType(List.map (parameter f) ps, Option.map (varParameter f) v)

        and constraints f x = fields f x

        and fields f x = sourced f x <| fun (Fields fs) ->
            Fields <| NonEmptyList.map (field f) fs

        and field f x = sourced f x <| fun (Field(k, t)) ->
            Documents.Field(sourced f k id, typeSign f t)

        and parameter f x = sourced f x <| fun (Parameter(n, t)) ->
            Parameter(Option.map (name f) n, typeSign f t)

        and varParameter f x = sourced f x <| fun (VariadicParameter(n, c)) ->
            VariadicParameter(Option.map (name f) n, Option.map (typeSign f) c)

        let typeParameter f x = sourced f x <| function
            | TypeParameter(n, c) -> TypeParameter(name f n, Option.map (constraints f) c)
            | VariadicTypeParameter(n, c) -> VariadicTypeParameter(name f n, Option.map (typeSign f) c)

        let tag f x = sourced f x <| function
            | UnknownTag(n, c) -> UnknownTag(name f n, comment f c)
            | TypeTag t -> TypeTag(typeSign f t)
            | GlobalTag(n, t) -> GlobalTag(name f n, typeSign f t)
            | FeatureTag n -> FeatureTag(name f n)
            | ClassTag(n, t) -> ClassTag(name f n, Option.map (typeSign f) t)
            | FieldTag(v, n, t) -> FieldTag(v, fieldKey f n, typeSign f t)
            | GenericTag ps -> GenericTag <| NonEmptyList.map (typeParameter f) ps

        let document f x = sourced f x <| fun (Document(c, xs)) ->
            Document(comment f c, List.map (tag f) xs)

    let normalize ds =
        List.map (Mapping.document ((fun _ -> Span.empty), (fun _ -> Trivia.createEmpty()))) ds

    let withEmptyTrivia k = { kind = k; trivia = Trivia.createEmpty() }
    let withEmptySpan k = { kind = k; trivia = Span.empty }
    let comment x = x |> withEmptySpan |> Comment
    let printConfig = {
        leadingNoise = NonNull ""
        trailingNoise = NonNull ""
        options = Options.defaultOptions
    }
    let name n = n |> withEmptyTrivia |> Name
    let document c ans = Document(comment c, ans) |> withEmptySpan
    let fields = function
        | [] -> failwithf "empty list"
        | x::xs ->
            NonEmptyList(x, xs)
            |> NonEmptyList.map (fun (k, t) ->
                Documents.Field(withEmptySpan k, t)
                |> withEmptySpan
            )
            |> Fields
            |> withEmptySpan

    let toStringKey = List.map (fun (k, t) -> FieldKey.String k, t)
    let stringFields = toStringKey >> fields

    let type0 n = NamedType(name n, []) |> withEmptySpan
    let interfaceType = fields >> InterfaceType >> withEmptySpan
    let stringInterfaceType = toStringKey >> interfaceType

    let multiTypeCore ts v = MultiType(ts, v) |> withEmptySpan
    let multiType ts = multiTypeCore ts None
    /// ts, v
    let multiTypeV ts v = multiTypeCore ts (Some v)
    /// t[]
    let arrayType = ArrayType >> withEmptySpan
    /// fun(ts1, v1): ts2, v2
    let functionTypeCore (ts1, v1) (ts2, v2) = FunctionType(multiTypeCore ts1 v1, multiTypeCore ts2 v2) |> withEmptySpan
    /// fun(ts1): ts2
    let functionType ts1 ts2 = FunctionType(multiType ts1, multiType ts2) |> withEmptySpan
    /// name...: elemType
    let varParamCore name elemType = VariadicParameter(name, elemType) |> withEmptySpan
    /// ...: elemType
    let varParamE elemType = varParamCore None (Some elemType)
    /// ...
    let varParam = varParamCore None None
    let param t = Parameter(None, t) |> withEmptySpan
    let paramN n t = Parameter(Some(name n), t) |> withEmptySpan

    let genericTag = function
        | [] -> failwithf "empty list"
        | x::xs -> NonEmptyList(x, xs) |> GenericTag |> withEmptySpan

    let typeParameterFs n fs = TypeParameter(name n, Some fs) |> withEmptySpan

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
                                UnknownTag(
                                    Name {
                                        kind = "a"
                                        trivia = {
                                            leadingTriviaLength = 0
                                            span = { start = 4; end' = 5 }
                                            trailingTriviaLength = 0
                                            leadingDocument = None
                                            trailingDocument = None
                                        }
                                    },
                                    Comment {
                                        kind = ""
                                        trivia = { start = 5; end' = 5 }
                                    }
                                )
                            trivia = { start = 3; end' = 4 }
                        }
                    ]
                )
            trivia = { start = 3; end' = 4 }
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
    let source = print options expected
    let sourceWithNoise = n2 + source + n1
    let actual = parseRange sourceWithNoise n2.Length source.Length
    equalsWithMessage (normalize actual, normalize expected) "sourceWithNoise = %A" sourceWithNoise

let typeSignRoundTripTest expected =
    roundTripTest printConfig [document "" [withEmptySpan <| TypeTag expected]]

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

let [<Fact(DisplayName = "---@a a")>] simpleUnknownTag() =
    [
        document "" [
            UnknownTag(name "a", comment "a") |> withEmptySpan
        ]
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
            UnknownTag(name "a", comment "\f") |> withEmptySpan
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
            TypeTag(type0 "a") |> withEmptySpan
            TypeTag(type0 "a") |> withEmptySpan
        ]
    ]
    |> roundTripTest printConfig

let [<Fact(DisplayName = "--[[---@type { [=[]=]: a }]]")>] longStringInLongDocument() =
    [
        document "" [
            TypeTag(stringInterfaceType [
                "", type0 "a"
            ])
            |> withEmptySpan
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
            TypeTag(stringInterfaceType [
                "]=]", type0 "a"
            ])
            |> withEmptySpan
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
                None,
                FieldKey.String "" |> withEmptySpan,
                type0 "a"
            )
            |> withEmptySpan
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
            TypeTag(stringInterfaceType [
                "\n", type0 "a"
            ])
            |> withEmptySpan
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
            TypeTag(arrayType (type0 "a"))
            |> withEmptySpan
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

let [<Fact(DisplayName = "---@type (fun(): ...: a)[]")>] funTypeConstrainedVarResultInArrayType() =
    arrayType (functionTypeCore ([], None) ([], Some(varParamE (type0 "a"))))
    |> typeSignRoundTripTest

let [<Fact(DisplayName = "---@type { \"\\n\": a }")>] constrainedType() =
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
            GlobalTag(name "a", type0 "a") |> withEmptySpan
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
    NamedType(name "a", [type0 "x"; type0 "y"])
    |> withEmptySpan
    |> typeSignRoundTripTest

let [<Fact(DisplayName = "---@type a<(x, y)>")>] multiType2InGeneric1() =
    multiType [param <| type0 "x"; param <| type0 "y"]
    |> typeSignRoundTripTest

let [<Fact(DisplayName = "---@type ...")>] multiTypeVar() =
    multiTypeV [] varParam
    |> typeSignRoundTripTest

let [<Fact(DisplayName = "---@type (p: t, ...)")>] withParameterName() =
    multiTypeV [paramN "p" <| type0 "t"] varParam
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
