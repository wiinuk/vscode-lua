
#load "PublicUnusedMemberAnalyzer.fsx"
open Argu
open Fake.IO.GlobbingPattern
open Fake.IO.Globbing.Operators
open System.Collections.Concurrent
open System.IO
open RichConsole
open PublicUnusedMemberAnalyzer

type Command =
    | Output_Path of string
    | Log_Level of LogLevel
with
    interface IArgParserTemplate with
        member _.Usage = ""

let args = ArgumentParser.Create(__SOURCE_FILE__).ParseCommandLine(fsi.CommandLineArgs.[1..])
args.TryGetResult <@ Log_Level @> |> Option.iter (fun l ->
    logLevel <- l
) 
if isDebug then printfn $"%A{fsi.CommandLineArgs}"

let outputPath = args.GetResult <@ Output_Path @>
let resources = None

let assemblyPaths = [
    yield! setBaseDir outputPath !!"LuaChecker*.dll"
    Path.Combine(outputPath, "server.dll")
]
if isDebug then printfn $"%A{assemblyPaths}"

let diagnostics = ConcurrentBag()
checkPublicUnusedMembers diagnostics assemblyPaths assemblyPaths
for d in diagnostics do printDiagnostic resources d

if diagnostics |> Seq.exists (fun d -> Hint < d.severity) then
    exit -1
