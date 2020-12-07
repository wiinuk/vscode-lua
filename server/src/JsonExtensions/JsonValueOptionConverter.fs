namespace LuaChecker.Text.Json.Serialization
open System
open System.Reflection
open System.Text.Json
open System.Text.Json.Serialization


[<Sealed>]
type JsonConverterValueOption<'T>(options: JsonSerializerOptions) =
    inherit JsonConverter<'T voption>()

    let valueType = typeof<'T>
    let valueConverter = options.GetConverter valueType :?> JsonConverter<'T>

    override _.Read(reader, _, options) =
        match reader.TokenType with
        | JsonTokenType.Null -> ValueNone
        | _ -> ValueSome <| valueConverter.Read(&reader, valueType, options)

    override _.Write(writer, value, options) =
        match value with
        | ValueNone -> writer.WriteNullValue()
        | ValueSome value -> valueConverter.Write(writer, value, options)

[<Sealed>]
type JsonValueOptionConverter() =
    inherit JsonConverterFactory()

    override _.CanConvert toType = toType.IsGenericType && toType.GetGenericTypeDefinition() = typedefof<voption<_>>
    override f.CreateConverter(toType, options) =
        let t = toType.GetGenericArguments().[0]
        downcast Activator.CreateInstance(
            typedefof<JsonConverterValueOption<_>>.MakeGenericType [| t |],
            BindingFlags.Instance ||| BindingFlags.Public,
            binder = null,
            args = [|options|],
            culture = null
        )
