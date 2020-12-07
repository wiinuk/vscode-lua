module LuaChecker.Text.Json.Serialization.Tests
open FsCheck
open LuaChecker.Text.Json
open System.Text.Json
open Xunit


let checkConfig = {
    Config.QuickThrowOnFailure with
        QuietOnSuccess = true
}
let check test = Check.One(checkConfig, test)
let (=?) l r = if not (l = r) then Assert.True(false, sprintf "%A =? %A" l r)

let makeOptions() =
    let options = JsonSerializerOptions()
    options.Converters.Add <| JsonFSharpRecordConverter()
    options.Converters.Add <| JsonFSharpRecordOptionalFieldConverter()
    options

type Point = {
    x: int
    y: int
}

[<Fact>]
let ``F# record round-trip`` () =
    let options = makeOptions()
    check <| fun (x: Point) -> JsonSerializer.Deserialize(JsonSerializer.Serialize(x, options), options) =? x

[<Struct>]
type ValuePoint = {
    X: int
    Y: int
}
[<Fact>]
let ``F# struct record round-trip`` () =
    let options = makeOptions()
    check <| fun (x: ValuePoint) -> JsonSerializer.Deserialize(JsonSerializer.Serialize(x, options), options) =? x

[<Fact>]
let ``F# anonymous record round-trip`` () =
    let options = makeOptions()
    check <| fun (x: {| name: string; age: int; book: {| title: string; page: int |} |}) ->
        JsonSerializer.Deserialize(JsonSerializer.Serialize(x, options), options) =? x

[<Fact>]
let ``F# struct anonymous record round-trip`` () =
    let options = makeOptions()
    check <| fun (x: struct {| name: string; age: int; book: struct {| title: string; page: int |} |}) ->
        JsonSerializer.Deserialize(JsonSerializer.Serialize(x, options), options) =? x

[<Fact>]
let ``F# record containing array round-trip``() =
    let options = makeOptions()
    check <| fun (x: {| books: int array |}) ->
        JsonSerializer.Deserialize(JsonSerializer.Serialize(x, options), options) =? x

[<Fact>]
let ``F# record in array round-trip``() =
    let options = makeOptions()
    check <| fun (x: struct {| x: int; y: int |} array) ->
        JsonSerializer.Deserialize(JsonSerializer.Serialize(x, options), options) =? x

[<Fact>]
let ``optional field in F# record``() =
    let options = makeOptions()
    let serialize x = JsonSerializer.Serialize(x, options)
    let deserialize x = JsonSerializer.Deserialize(json = x, options = options)

    serialize {| age = Defined 45 |} =? """{"age":45}"""
    serialize {| age = (Undefined: int OptionalField) |} =? """{}"""

    deserialize """{"age":20}""" =? {| age = Defined 20 |}
    deserialize """{}""" =? {| age = (Undefined: int OptionalField) |}
    (fun () -> (deserialize """{"age":null}""": {| age: int OptionalField |}) |> ignore)
        |> Assert.ThrowsAny<JsonException>
        |> ignore

    check <| fun (x: struct {| age: int OptionalField |}) ->
        deserialize(serialize x) =? x

[<Fact>]
let optionalFieldOfArray() =
    let options = makeOptions()
    let serialize x = JsonSerializer.Serialize(x, options)
    let deserialize x = JsonSerializer.Deserialize(json = x, options = options)

    serialize {| f = Defined [|1|] |} =? """{"f":[1]}"""
    deserialize """{"f":[2]}""" =? {| f = Defined [|2|] |}
