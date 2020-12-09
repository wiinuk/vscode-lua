namespace LuaChecker.Text.Json

[<Struct>]
type OptionalField<'T> =
    | Undefined
    | Defined of 'T

module OptionalField =
    let defaultValue v = function Defined x -> x | _ -> v
    let ofOption = function Some x -> Defined x | _ -> Undefined
    let toOption = function Defined x -> Some x | _ -> None

namespace LuaChecker.Text.Json.Serialization.Internal
open LuaChecker.Text.Json
open System
open System.Collections.Generic
open System.Runtime.CompilerServices
open System.Text
open System.Text.Json
open System.Text.Json.Serialization


type FSharpRecordFieldConverter<'F> = {
    Utf8Name: byte array
    Type: Type
    /// allow null
    Converter: 'F JsonConverter
    IsOptional: bool
}

[<AutoOpen>]
module internal JsonSerializerOptionExtensions =
    [<AbstractClass; Sealed>]
    type private DefaultConverterHolder<'T> private() =
        static let value = { new JsonConverter<'T>() with
            override _.Write(w, v, options) = JsonSerializer.Serialize(w, v, options)
            override _.Read(r, _, options) = JsonSerializer.Deserialize(&r, options)
        }
        static member Value = value

    type JsonSerializerOptions with
        [<RequiresExplicitTypeArguments>]
        member options.GetConverterOrDefaultConverter<'T>() =
            match options.GetConverter typeof<'T> with
            | :? JsonConverter<'T> as x -> x
            | _ -> DefaultConverterHolder<_>.Value

module JsonConverterFSharpRecord =
    type internal Marker = class end

    [<RequiresExplicitTypeArguments>]
    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let createField<'F> (name: string) (options: JsonSerializerOptions) =
        let t = typeof<'F>
        {
            Utf8Name = Encoding.UTF8.GetBytes name
            Type = t
            Converter = options.GetConverterOrDefaultConverter<'F>()
            IsOptional = t.IsGenericType && t.GetGenericTypeDefinition() = typedefof<OptionalField<_>>
        }
    /// `{`
    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let readStartRecord(reader: Utf8JsonReader byref) =
        if reader.TokenType <> JsonTokenType.StartObject then raise <| JsonException()

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let readIsPropertyWithVerify (reader: Utf8JsonReader byref) =
        if reader.Read() then
            match reader.TokenType with
            | JsonTokenType.EndObject -> false
            | JsonTokenType.PropertyName -> true
            | _ -> raise <| JsonException()
        else
            raise <| JsonException()

    /// `"fieldName": field`
    [<RequiresExplicitTypeArguments>]
    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let tryReadField<'F> (reader: Utf8JsonReader byref) options field (result: 'F byref) =
        if reader.ValueTextEquals(ReadOnlySpan field.Utf8Name) then
            reader.Read() |> ignore
            result <-
                match field.Converter with
                | null -> JsonSerializer.Deserialize(&reader, options)
                | converter -> converter.Read(&reader, field.Type, options)
            true
        else
            false

    /// `"anyName": anyJson`
    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let skipAnyProperty(reader: Utf8JsonReader byref) =
        if reader.TokenType <> JsonTokenType.PropertyName then raise <| JsonException()
        reader.Skip()
        reader.Skip()

    [<RequiresExplicitTypeArguments>]
    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let writeField<'F> (writer: Utf8JsonWriter) field (value: 'F) options =
        if field.IsOptional && EqualityComparer.Default.Equals(value, Unchecked.defaultof<'F>) then () else

        writer.WritePropertyName(ReadOnlySpan field.Utf8Name)
        match field.Converter with
        | null -> JsonSerializer.Serialize(writer, value, options)
        | converter -> converter.Write(writer, value, options)
