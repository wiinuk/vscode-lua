module LuaChecker.Server.Json
open LuaChecker.Primitives
open LuaChecker.Server.Protocol
open LuaChecker.Text.Json.Serialization
open System.Text.Json
open System.Runtime.CompilerServices
open System.Diagnostics.CodeAnalysis


let internal options =
    let options = JsonSerializerOptions()
    options.Converters.Add <| JsonStringEnumConverter<JsonRpcVersion>()
    options.Converters.Add <| JsonStringEnumConverter<Methods>()
    options.Converters.Add <| JsonStringEnumConverter<MarkupKind>()
    options.Converters.Add <| JsonValueOptionConverter()
    options.Converters.Add <| JsonFSharpRecordConverter()
    options.Converters.Add <| JsonFSharpRecordOptionalFieldConverter()
    options

[<RequiresExplicitTypeArguments; MethodImpl(MethodImplOptions.AggressiveInlining)>]
let deserialize<'T> uft8Json: 'T = JsonSerializer.Deserialize(utf8Json = uft8Json, options = options)
let serialize value = JsonSerializer.SerializeToUtf8Bytes(value, options)
[<SuppressMessage("UnusedMemberAssemblyAnalyzer", "AA0001:MemberUnused")>]
let serializeWriter writer value = JsonSerializer.Serialize(writer, value, options)

module Utf8Serializable =
    [<Struct>]
    type ProtocolValueIsUtf8SerializableByJson<'T> =
        interface IUtf8SerializableShape<'T> with
            member _.Deserialize utf8Bytes = deserialize<'T> utf8Bytes

    let protocolValue<'T> = the<ProtocolValueIsUtf8SerializableByJson<'T>>
