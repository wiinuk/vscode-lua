#r "nuget: System.Text.Json"
#r "nuget: System.Xml.XDocument"
#r "System.Xml.Linq"
#r "../checker/bin/Debug/netstandard2.1/LuaChecker.Checker.dll"
#r "../LuaChecker.Syntax/bin/Debug/netstandard2.1/LuaChecker.Syntax.dll"
#r "../Protocol/bin/Debug/netstandard2.1/LuaChecker.Protocol.dll"
#r "../Protocol/bin/Debug/netstandard2.1/LuaChecker.JsonExtensions.dll"
open FSharp.Reflection
open LuaChecker.Server.Protocol
open System
open System.IO
open System.Text.Json
open System.Xml
open System.Xml.Linq


type OtherMessages =
    | GenericTypeParameters
    | GenericTypeSubstitute of typeParameterName: string * typeName: string
    | OtherFieldLocation
    | OtherTagLocation

type ServerMessages =
    | LoadResourceFrom of resourcePath: string
    | ServerStarting
    | ServerTerminatedNormally

    | RequestCanceled of requestId: int
    | MessageParseError of error: MessageReader.ErrorKind
    | ReceivedExitNotification
    | MessageReceived of message: JsonRpcMessage<JsonElement, Methods, JsonElement>
    | UnknownRequest of requestId: int * method: Methods * ``params``: JsonElement
    | UnknownNotification of method: Methods * ``params``: JsonElement
    | InvalidMessageFormat of message: JsonRpcMessage<JsonElement, Methods, JsonElement>
    | ErrorResponseReceived of error: JsonRpcResponseError option
    | ResponseHandlerNotFound of id: int * result: JsonElement
    | ResourceValidationError of message: string
    | MessageSending of json: string

let makeFormatPattern parameterCount =
    let chars0 = @"([^{}]|\{\{|\}\})*"
    if parameterCount = 0 then chars0 else

    let indexes = seq { for i in 0..parameterCount-1 do string i }
    let indexes =
        if parameterCount <= 10
        then indexes |> String.concat "" |> sprintf "[%s]"
        else indexes |> String.concat "|" |> sprintf "(%s)"

    sprintf @"%s(\{%s\}%s)*" chars0 indexes chars0

let typeToName = dict [
    typeof<string>, "string"
    typeof<int>, "int"
]
type MessageCategory =
    | DiagnosticMessages
    | LogMessages

type FormatDescription = {
    ``type``: string
    description: string
    pattern: string
    caseName: string
    parameterCount: int

    category: MessageCategory
}
module JsonScheme =
    let unionCaseFormatSchemes<'T> category = seq {
        for c in FSharpType.GetUnionCases typeof<'T> do
            let fs = c.GetFields()
            let fieldDescriptions = seq {
                for f in fs do
                    let name = f.Name
                    let t = f.PropertyType
                    let formattableType =
                        if typeof<IFormattable>.IsAssignableFrom t || typeof<IConvertible>.IsAssignableFrom t
                        then t
                        else typeof<string>

                    let formattableTypeName =
                        match typeToName.TryGetValue formattableType with
                        | true, n -> n
                        | _ -> formattableType.Name

                    if name.StartsWith "Item" then formattableTypeName
                    else sprintf "%s: %s" name formattableTypeName
            }
            (c.DeclaringType, c.Name),
            {
                ``type`` = "string"
                description = Seq.foldBack (sprintf "%s -> %s") fieldDescriptions "string"
                pattern = makeFormatPattern fs.Length
                caseName = c.Name
                parameterCount = fs.Length
                category = category
            }
    }
    let fleshName xs knownNames =
        let name = xs |> Seq.find (fun x -> not <| Set.contains x knownNames)
        name, Set.add name knownNames

    let makeNames (t: Type) (caseName: string) = seq {
        caseName
        let n = t.Name + "." + caseName
        n
        let mutable n = n
        let mutable dt = t
        while (dt <- dt.DeclaringType; not <| isNull dt) do
            n <- dt.Name + "." + n
            n

        let n = t.Namespace + "." + n
        n

        sprintf "[%s]%s" (t.Assembly.GetName().Name) n
        sprintf "[%s]%s" t.Assembly.FullName n
    }

    let uniqueNames =
        Seq.concat
        >> Seq.mapFold (fun knownNames ((t, caseName), desc) ->
            let name, knownNames = fleshName (makeNames t caseName) knownNames
            (name, desc), knownNames
        ) Set.empty
        >> fst
        >> Seq.cache

    let cases = uniqueNames [
        unionCaseFormatSchemes<LuaChecker.Syntax.ParseError> DiagnosticMessages
        unionCaseFormatSchemes<LuaChecker.TypeSystem.UnifyError> DiagnosticMessages
        unionCaseFormatSchemes<LuaChecker.DiagnosticKind> DiagnosticMessages
        unionCaseFormatSchemes<LuaChecker.Severity> DiagnosticMessages
        unionCaseFormatSchemes<LuaChecker.DeclarationKind> DiagnosticMessages
        unionCaseFormatSchemes<OtherMessages> DiagnosticMessages
        unionCaseFormatSchemes<ServerMessages> LogMessages
    ]

    let schema() =
        {|
        ``$schema`` = "http://json-schema.org/schema"
        ``type`` = "object"
        properties = Map cases
        required = Seq.map fst cases
        |}

    let write path =
        let options = JsonSerializerOptions(WriteIndented = true)
        File.WriteAllText(
            contents = JsonSerializer.Serialize(schema(), options),
            path = path
        )
        printfn "%s -> %s" __SOURCE_FILE__ <| Path.GetFullPath path

module Xsd =
    let e name = XElement(name = name)
    let n name = XName.Get name
    let (%=) (x: XElement) (name, value) = x.SetAttributeValue(name, value); x
    let (</) (x: XElement) (child: XElement) = x.Add child; x
    let (?) (ns: XNamespace) n = ns + n
    let (+=) (x: XElement) (child: string) = x.Add child; x


    let xsd = XNamespace.Get "http://www.w3.org/2001/XMLSchema"

    let autoNaming prefix key makeValue map =
        match Map.tryFind key map with
        | Some(name, _) -> name, map
        | None ->
            let name = sprintf "%s%d" prefix <| Map.count map + 1
            name, Map.add key (name, makeValue key name) map

    let patternSimpleType pattern name =
        e xsd?simpleType %= (n"name", name)
        </ (e xsd?restriction %= (n"base", "xsd:string")
            </ e xsd?pattern %= (n"value", pattern)
        )

    let messageFormatElement (parent, patternToTypeDef) (caseName, d) =
        let typeName, patternToTypeDef = autoNaming "pattern-" d.pattern patternSimpleType patternToTypeDef
        let element =
            e xsd?element %= (n"name", XmlConvert.EncodeLocalName caseName) %= (n"type", typeName)
            </ (e xsd?annotation
                </ e xsd?documentation += d.description
            )
        parent </ element, patternToTypeDef

    let categoryToXmlName = function
        | DiagnosticMessages -> "diagnostic-messages"
        | LogMessages -> "log-messages"

    let schema() =
        let makeMessagesType patternToTypeDef (category, cases) =
            let all, patternToTypeDef = Seq.fold messageFormatElement (e xsd?all, patternToTypeDef) cases
            let messagesType = e xsd?complexType %= (n"name", categoryToXmlName category) </ all
            messagesType, patternToTypeDef

        let categoryAndMessages = JsonScheme.cases |> Seq.groupBy (fun (_, d) -> d.category)
        let patternToTypeDef = Map.empty
        let messagesTypes, patternToTypeDef =
            categoryAndMessages
            |> Seq.mapFold makeMessagesType patternToTypeDef

        let addMessagesTypeRef parent =
            categoryAndMessages
            |> Seq.fold (fun parent (category, _) ->
                let categoryName = categoryToXmlName category
                parent
                </ e xsd?element
                    %= (n"name", categoryName)
                    %= (n"type", categoryName)
            ) parent

        let resourcesElement =
            e xsd?element %= (n"name", "resources")
            </ (e xsd?complexType
                </ addMessagesTypeRef (e xsd?all)
            )

        let addMessageTypes parent = Seq.fold (</) parent messagesTypes

        let schema' =
            e xsd?schema %= (XNamespace.Xmlns?xsd, xsd)
            </ resourcesElement
            |> addMessageTypes

        patternToTypeDef
        |> Map.fold (fun schema _ (_, patternSimpleType) ->
            schema </ patternSimpleType
        ) schema'

    let ivResources() =
        let xsi = XNamespace.Get "http://www.w3.org/2001/XMLSchema-instance"

        let messageElements cases = seq {
            for key, m in cases do
                let caseName = m.caseName.Replace("}", "}}").Replace("{", "{{")
                let parameters = String.concat ", " <| seq {
                    for i in 0..m.parameterCount-1 ->
                        sprintf "{%d}" i
                }
                let parameters =
                    match parameters with
                    | "" -> ""
                    | _ -> "(" + parameters + ")"

                let content = caseName + parameters
                let name = XmlConvert.EncodeLocalName key
                XElement(n name, XText content)
        }
        let messagesElement (category, cases) =
            let parentElement = e (n (categoryToXmlName category))
            Seq.fold (</) parentElement (messageElements cases)

        let categoryAndMessages = JsonScheme.cases |> Seq.groupBy (fun (_, d) -> d.category)
        let messagesElements = categoryAndMessages |> Seq.map messagesElement

        let resources = e (n"resources") %= (xsi?noNamespaceSchemaLocation, "resources.xsd")
        Seq.fold (</) resources messagesElements

    let writeXml path (doc: XDocument) =
        use s = new MemoryStream()
        let nl = "\n"
        let encoding = System.Text.UTF8Encoding(encoderShouldEmitUTF8Identifier = false)
        do
            let settings =
                XmlWriterSettings(
                    NewLineChars = nl,
                    Indent = true,
                    NewLineHandling = NewLineHandling.Entitize,
                    Encoding = encoding
                )
            use w = XmlWriter.Create(s, settings)
            doc.WriteTo w
        let nl = encoding.GetBytes nl
        s.Write(nl, 0, nl.Length)
        s.Flush()
        File.WriteAllBytes(path, s.ToArray())
        printfn "%s -> %s" __SOURCE_FILE__ <| Path.GetFullPath path

    let write xsdPath ivXmlPath =
        schema() |> XDocument |> writeXml xsdPath
        ivXmlPath |> Option.iter (fun ivXmlPath -> ivResources() |> XDocument |> writeXml ivXmlPath)
#if GEN
do
#else
lazy do
#endif
    let ivXmlPath =
        match List.ofArray fsi.CommandLineArgs with
        | _::"--schema-only"::_ -> None
        | _ -> Some "./resources.xml"

    Xsd.write "./resources.xsd" ivXmlPath
