module LuaChecker.Server.JsonElement
open LuaChecker.Server.Protocol
open LuaChecker.Text.Json
open LuaChecker.Text.Json.Parsing


let private options = ParserOptions.createFromParsers [
    JsonRegistrationParserFactory()
    FSharpRecordParserFactory()
    FSharpOptionParserFactory()
    FSharpValueOptionParserFactory()
    FSharpRecordOptionalFieldParserFactory()
    FSharpUnitParser()
]
let parse<'T> e = JsonElementParser.parse<'T> options e
