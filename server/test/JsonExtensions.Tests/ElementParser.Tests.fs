module LuaChecker.Text.Json.Parsing.Tests
open LuaChecker.Text.Json
open LuaChecker.Text.Json.Serialization.Tests
open System.Text.Json
open Xunit
open System


let makeOptions() = ParserOptions.createFromParsers [
    FSharpValueOptionParserFactory()
    FSharpRecordParserFactory()
    FSharpUnitParser()
    FSharpRecordOptionalFieldParserFactory()
]

let parseJsonElement json =
    use doc = JsonDocument.Parse(json + "")
    doc.RootElement.Clone()

let private makeFSharpParser() = parseJsonElement >> JsonElementParser.parse<_> (makeOptions())

[<Fact>]
let voptionParser() =
    let parse = makeFSharpParser()

    parse "null" =? ValueNone
    parse "123" =? ValueSome 123

[<Fact>]
let uriElementParser() =
    let parse = makeFSharpParser()

    parse "null" =? null
    parse "\"https://example.com\"" =? Uri "https://example.com"
    parse "\"C:/dir/file.ext\"" =? Uri "C:/dir/file.ext"

[<Fact>]
let structRecordParser() =
    let parse = makeFSharpParser()

    parse """{"name":"bob","age":20,"book":{"title":"aaa"}}""" =? struct {| name = "bob"; age = 20; book = struct {| title = "aaa" |} |}

[<Fact>]
let recordParser() =
    let parse = makeFSharpParser()

    parse """{"name":"bob","age":20,"book":{"title":"aaa"}}""" =? {| name = "bob"; age = 20; book = {| title = "aaa" |} |}

[<Fact>]
let arrayParser() =
    let parse = makeFSharpParser()

    parse """[1,2,3]""" =? [|1;2;3|]

[<Fact>]
let unitParser() =
    let parse = makeFSharpParser()
    parse "null" =? ()
    parse "123" =? ()
    parse "[]" =? ()
    parse "[true]" =? ()
    parse "{}" =? ()
    parse """{"a":false}""" =? ()

    JsonElementParser.parse<_> (makeOptions()) (JsonElement()) =? ()

[<Fact>]
let optionalFieldParser() =
    let parse = makeFSharpParser()
    parse """{"age":10}""" =? {| age = Defined 10 |}
    parse """{}""" =? {| age = (Undefined: int OptionalField) |}
    Assert.ThrowsAny<exn>(fun () -> (parse """{"age":null}""" : {| age: int OptionalField |}) |> ignore) |> ignore
