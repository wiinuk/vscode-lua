namespace LuaChecker.Text.Json.Serialization
open System
open System.Collections.Generic
open System.Text
open System.Text.Json
open System.Text.Json.Serialization


[<Sealed>]
type JsonStringEnumConverter<'E when 'E :> Enum and 'E : struct and 'E : equality>() =
    inherit JsonConverter<'E>()

    let nameAndValues, nameToValue, valueToName =
        let nameAndValues = [|
            for v in typeof<'E>.GetEnumValues() do
                let name = typeof<'E>.GetEnumName v
                let utf8Name = Encoding.UTF8.GetBytes name
                struct {| name = name; utf8Name = utf8Name; value = v :?> 'E |}
        |]
        let valueToName = Dictionary()
        for e in nameAndValues do
            valueToName.Add(e.value, e.utf8Name)

        if 8 < nameAndValues.Length then
            let nameToValue = Dictionary()
            for e in nameAndValues do
                nameToValue.Add(e.name, e.value)
            null, nameToValue, valueToName
        else
            nameAndValues, null, valueToName

    let readByHashTable (reader: Utf8JsonReader byref) =
        let mutable result = Unchecked.defaultof<_>
        if nameToValue.TryGetValue(reader.GetString(), &result)
        then result
        else raise <| JsonException()

    override _.Read(reader, _, _) =
        if reader.TokenType <> JsonTokenType.String then raise <| JsonException() else

        match nameAndValues with
        | null -> readByHashTable &reader
        | enums ->

        let mutable i = 0
        let mutable result = Unchecked.defaultof<_>
        while
            if enums.Length <= i then
                raise <| JsonException()
            else
                let e = &enums.[i]
                if reader.ValueTextEquals(ReadOnlySpan e.utf8Name) then
                    result <- e.value
                    false
                else
                    true
            do i <- i + 1
        result

    override _.Write(writer, value, _) =
        let mutable utf8Name = null
        if valueToName.TryGetValue(value, &utf8Name) then
            writer.WriteStringValue(ReadOnlySpan utf8Name)
        else
            writer.WriteStringValue(value.ToString())
