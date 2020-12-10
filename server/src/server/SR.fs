namespace LuaChecker.Server
open FSharp.Data
open LuaChecker.Server.Log
open System.Globalization
open System
open System.IO
open System.Xml.Linq
open System.Xml.Schema


type ServerResources = XmlProvider<Schema = "resources.xsd">
module ServerResources =
    let validateXml (xml: XDocument) (schema: XmlSchemaSet) =
        let mutable validationException = None
        xml.Validate(schema, fun _ e -> match e.Severity with XmlSeverityType.Warning -> () | _ -> validationException <- Some e.Exception)
        validationException

    let loadFile resourcePaths =
        let cultures = seq {
            CultureInfo.CurrentUICulture
            CultureInfo.CurrentCulture
            CultureInfo.InstalledUICulture
        }
        let cultures = seq {
            for c in cultures do
                if not (isNull c) && not c.IsNeutralCulture && c.Name <> "en-US" then
                    c
        }
        let suffixes = seq {
            match Seq.tryHead cultures with
            | Some c -> "." + c.Name.ToLower()
            | _ -> ()

            ".en-us"
            ".en"
            "." + CultureInfo.InvariantCulture.TwoLetterISOLanguageName.ToLower()
            ""
        }
        let paths = seq {
            yield! resourcePaths
            for suffix in suffixes -> sprintf "./resources%s.xml" suffix
        }
        let resource = Seq.head <| seq {
            for path in paths do
                let r =
                    try
                        let resource = ServerResources.Load path
                        ifInfo { Log.Format(resource.LogMessages.LoadResourceFrom, Path.GetFullPath(Path.Combine(Environment.CurrentDirectory, path))) }
                        Ok resource

                    with e -> Error e

                match r with
                | Ok x -> x
                | Error _ -> ()
        }
        match validateXml resource.XElement.Document <| ServerResources.GetSchema() with
        | Some validationException ->
            ifWarn { Log.Format(resource.LogMessages.ResourceValidationError, validationException.Message) }
        | _ -> ()

        resource
