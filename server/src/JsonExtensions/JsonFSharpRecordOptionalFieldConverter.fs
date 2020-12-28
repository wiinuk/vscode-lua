namespace LuaChecker.Text.Json.Serialization
open LuaChecker.Text.Json
open LuaChecker.Text.Json.Serialization.Internal
open System
open System.Reflection
open System.Text.Json
open System.Text.Json.Serialization


[<Sealed>]
type private JsonFSharpRecordOptionalFieldConverter<'T>(options: JsonSerializerOptions) =
    inherit JsonConverter<'T OptionalField>()

    let valueType = typeof<'T>
    let valueConverter = options.GetConverterOrDefaultConverter<'T>()

    override _.Read(reader, _, options) =
        Defined(valueConverter.Read(&reader, valueType, options))

    override _.Write(writer, value, options) =
        match value with
        | Defined value -> valueConverter.Write(writer, value, options)
        | Undefined -> raise <| JsonException()

[<Sealed>]
type JsonFSharpRecordOptionalFieldConverter() =
    inherit JsonConverterFactory()

    override _.CanConvert toType = toType.IsGenericType && toType.GetGenericTypeDefinition() = typedefof<OptionalField<_>>
    override f.CreateConverter(toType, options) =
        let t = toType.GetGenericArguments().[0]
        downcast Activator.CreateInstance(
            typedefof<JsonFSharpRecordOptionalFieldConverter<_>>.MakeGenericType [| t |],
            BindingFlags.Instance ||| BindingFlags.Public,
            binder = null,
            args = [|options|],
            culture = null
        )
