namespace LuaChecker.Server
open FSharp.Data
open LuaChecker.Server.Log
open System.Globalization
open System
open System.IO


type ServerResources = XmlProvider<Schema = "resources.xsd">
module ServerResources =
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
        Seq.head <| seq {
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
