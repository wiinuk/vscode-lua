#r "nuget: Fake.Core.Process"
#r "nuget: FSharp.Data"
open Fake.Core
open FSharp.Data
open System.IO

let [<Literal>] SettingsPath = __SOURCE_DIRECTORY__ + "/../src/supported-runtime-specs.json"
let projectPath = Path.Combine(__SOURCE_DIRECTORY__, "src/server/server.fsproj")

// ResourcesSchemaGen.fsx が参照できる位置にアセンブリをビルドする
CreateProcess.fromRawCommand "dotnet" ["build"; __SOURCE_DIRECTORY__]
    |> CreateProcess.ensureExitCode
    |> Proc.run
    |> ignore

for runtime in JsonProvider<SettingsPath>.Load SettingsPath do
    CreateProcess.fromRawCommand "dotnet" [
        "publish"
        projectPath
        "--configuration"; "Release"
        "--runtime"; runtime.Rid
        "--output"; Path.Combine(__SOURCE_DIRECTORY__, "bin", runtime.Rid)
        "-p:PublishSingleFile=true"
        "-p:GenerateDocumentationFile=false"
        "-p:IncludeNativeLibrariesForSelfExtract=true"
    ]
    |> CreateProcess.ensureExitCode
    |> Proc.run
    |> ignore
