namespace LuaChecker.Text.Json
open System
open System.Collections.Concurrent
open System.Collections.Generic
open System.Reflection
open System.Runtime.CompilerServices
open System.Text.Json


[<AbstractClass>]
type JsonElementParser() =
    abstract ParseUntyped: source: JsonElement * typeToParse: Type * options: ParserOptions -> obj
    abstract CanParse: typeToParse: Type -> bool

and ParserOptions = {
    typeToParser: ConcurrentDictionary<Type, JsonElementParser>
    parsers: JsonElementParser list
}

[<AbstractClass>]
type JsonElementParserFactory() =
    inherit JsonElementParser()
    abstract CreateParser: typeToParse: Type * options: ParserOptions -> JsonElementParser
    override x.ParseUntyped(e, typeToParse, options) = x.CreateParser(typeToParse, options).ParseUntyped(e, typeToParse, options)

[<AbstractClass>]
type JsonElementParser<'T>() =
    inherit JsonElementParser()

    abstract Parse: source: JsonElement * options: ParserOptions -> 'T

    override _.CanParse t = typeof<'T> = t
    override x.ParseUntyped(e, _, options) = upcast x.Parse(e, options)

[<Sealed>]
type Int32Parser() =
    inherit JsonElementParser<int>()
    override _.Parse(e, _) = e.GetInt32()

[<Sealed>]
type StringParser() =
    inherit JsonElementParser<string>()
    override _.Parse(e, _) = if e.ValueKind = JsonValueKind.Null then null else e.GetString()

[<Sealed>]
type UriParser() =
    inherit JsonElementParser<Uri>()
    override _.Parse(e, _) =
        if e.ValueKind = JsonValueKind.Null then null else
        e.GetString() |> Uri

[<Sealed>]
type BooleanParser() =
    inherit JsonElementParser<bool>()
    override _.Parse(e, _) = e.GetBoolean()

[<AutoOpen>]
module private JsonElementParserHelpers =
    let createParser t args =
        Activator.CreateInstance(
            t,
            BindingFlags.Instance ||| BindingFlags.Public,
            args = args,
            binder = null,
            culture = null
        )
        :?> JsonElementParser

    let private getParserOrRaiseNonCache = Func<_,_,_>(fun typeToParse options ->
        let parser = options.parsers |> Seq.tryFind (fun p -> p.CanParse typeToParse)
        match parser with
        | None -> failwithf "parser not found: %A" typeToParse.FullName
        | Some parser ->

        match parser with
        | :? JsonElementParserFactory as factory -> factory.CreateParser(typeToParse, options)
        | _ -> parser
    )
    let getParserOrRaise typeToParse options =
        options.typeToParser.GetOrAdd(typeToParse, getParserOrRaiseNonCache, options)

    [<RequiresExplicitTypeArguments>]
    let getTypedParserOrRaise<'T> options = getParserOrRaise typeof<'T> options :?> JsonElementParser<'T>

[<Sealed>]
type EnumToIntegerParser<'T when 'T :> Enum and 'T : struct>() =
    inherit JsonElementParser<'T>()
    static let typeCode = Type.GetTypeCode typeof<'T>
    override _.Parse(e, _) =
        if e.ValueKind <> JsonValueKind.Number then raise <| JsonException()

        match typeCode with
        | TypeCode.SByte -> let mutable r = e.GetSByte() in Unsafe.As &r
        | TypeCode.Byte -> let mutable r = e.GetByte() in Unsafe.As &r
        | TypeCode.Int16 -> let mutable r = e.GetInt16() in Unsafe.As &r
        | TypeCode.UInt16 -> let mutable r = e.GetUInt16() in Unsafe.As &r
        | TypeCode.Int32 -> let mutable r = e.GetInt32() in Unsafe.As &r
        | TypeCode.UInt32 -> let mutable r = e.GetUInt32() in Unsafe.As &r
        | TypeCode.Int64 -> let mutable r = e.GetInt64() in Unsafe.As &r
        | TypeCode.UInt64 -> let mutable r = e.GetUInt64() in Unsafe.As &r
        | _ -> raise <| JsonException()

[<Sealed>]
type EnumToStringParser<'T>() =
    inherit JsonElementParser<'T>()
    static let stringToValue =
        let map = Dictionary<string,'T>()
        for v in Enum.GetValues typeof<'T> do
            map.Add(Enum.GetName(typeof<'T>, v), v :?> 'T)
        map

    override _.Parse(e, _) =
        if e.ValueKind <> JsonValueKind.String then raise <| JsonException()
        let mutable result = Unchecked.defaultof<_>
        if not <| stringToValue.TryGetValue(e.GetString(), &result) then raise <| JsonException() else
        result

[<AttributeUsage(AttributeTargets.Class ||| AttributeTargets.Struct ||| AttributeTargets.Enum)>]
type JsonElementParserAttribute(parserType: Type) =
    inherit Attribute()
    member _.ParserType = parserType

type EnumParserFactory() =
    inherit JsonElementParserFactory()

    override _.CanParse t = t.IsEnum
    override _.CreateParser(t, _) =
        match t.GetCustomAttributes<JsonElementParserAttribute>() |> Seq.tryHead with
        | Some a -> createParser a.ParserType null
        | _ ->

        let t = typedefof<EnumToIntegerParser<AttributeTargets>>.MakeGenericType(t)
        createParser t null

type SZArrayParser<'T>(options) =
    inherit JsonElementParser<'T array>()

    let elementParser = getTypedParserOrRaise<'T> options
    override _.Parse(e, options) =
        match e.ValueKind with
        | JsonValueKind.Null -> null
        | JsonValueKind.Array ->
            match e.GetArrayLength() with
            | 0 -> Array.empty
            | length ->

            let items = Array.zeroCreate length
            let mutable e = e.EnumerateArray()
            let mutable i = 0
            let p = elementParser
            while e.MoveNext() do
                items.[i] <- p.Parse(e.Current, options)
                i <- i + 1
            items

        | _ -> raise <| JsonException()

type SZArrayParserFactory() =
    inherit JsonElementParserFactory()
    override _.CanParse t =

        // TODO: t.IsSZArray
        t.IsArray && t.GetArrayRank() = 1

    override _.CreateParser(t, options) =
        let t = typedefof<SZArrayParser<_>>.MakeGenericType(t.GetElementType())
        createParser t [|options|]

module ParserOptions =
    let private defaultParsers =
        let d = Dictionary()
        d.Add(typeof<int>, Int32Parser() :> JsonElementParser)
        d.Add(typeof<string>, StringParser())
        d.Add(typeof<bool>, BooleanParser())
        d.Add(typeof<Uri>, UriParser())
        d

    let private defaultFactories = [
        EnumParserFactory() :> JsonElementParser
        SZArrayParserFactory() :> _
    ]

    let getParserOrRaise typeToParse options = getParserOrRaise typeToParse options
    [<RequiresExplicitTypeArguments>]
    let getTypedParserOrRaise<'T> options = getTypedParserOrRaise<'T> options

    let create() = {
        parsers = defaultFactories
        typeToParser = ConcurrentDictionary defaultParsers
    }
    let createFromParsers parsers = {
        parsers = [yield! parsers; yield! defaultFactories]
        typeToParser = ConcurrentDictionary defaultParsers
    }

[<Sealed>]
type FSharpOptionParser<'T>(options) =
    inherit JsonElementParser<'T option>()
    let valueParser = getTypedParserOrRaise<'T> options
    override _.Parse(e, options) =
        if e.ValueKind = JsonValueKind.Null then None
        else Some(valueParser.Parse(e, options))

type FSharpOptionParserFactory() =
    inherit JsonElementParserFactory()

    override _.CanParse t = t.IsGenericType && t.GetGenericTypeDefinition() = typedefof<option<_>>
    override _.CreateParser(t, options) =
        let t = typedefof<FSharpOptionParser<_>>.MakeGenericType(t.GetGenericArguments())
        createParser t [|options|]

[<Sealed>]
type FSharpValueOptionParser<'T>(options) =
    inherit JsonElementParser<'T voption>()
    let valueParser = getTypedParserOrRaise<'T> options
    override _.Parse(e, options) =
        if e.ValueKind = JsonValueKind.Null then ValueNone
        else ValueSome(valueParser.Parse(e, options))

type FSharpValueOptionParserFactory() =
    inherit JsonElementParserFactory()
    override _.CanParse t = t.IsGenericType && t.GetGenericTypeDefinition() = typedefof<voption<_>>
    override _.CreateParser(t, options) =
        let t = typedefof<FSharpValueOptionParser<_>>.MakeGenericType(t.GetGenericArguments())
        createParser t [|options|]

type UncheckedDefaultParser<'T>() =
    inherit JsonElementParser<'T>()
    override _.Parse(_, _) = Unchecked.defaultof<'T>

type FSharpUnitParser() = inherit UncheckedDefaultParser<unit>()

type FSharpRecordOptionalFieldParser<'T>(options) =
    inherit JsonElementParser<'T OptionalField>()
    let valueParser = getTypedParserOrRaise<'T> options
    override _.Parse(e, options) = Defined(valueParser.Parse(e, options))

type FSharpRecordOptionalFieldParserFactory() =
    inherit JsonElementParserFactory()
    override _.CanParse t = t.IsGenericType && t.GetGenericTypeDefinition() = typedefof<OptionalField<_>>
    override _.CreateParser(t, options) =
        let t = typedefof<FSharpRecordOptionalFieldParser<_>>.MakeGenericType(t.GetGenericArguments())
        createParser t [|options|]

module JsonElementParser =
    [<RequiresExplicitTypeArguments>]
    let parse<'T> options source =
        let parser = ParserOptions.getParserOrRaise typeof<'T> options :?> JsonElementParser<'T>
        parser.Parse(source, options)
