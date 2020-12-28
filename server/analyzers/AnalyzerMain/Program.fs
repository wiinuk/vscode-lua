open Argu
open Fake.IO.GlobbingPattern
open Fake.IO.Globbing.Operators
open LuaChecker.Analyzers.RichConsole
open LuaChecker.Analyzers.UnusedMemberAssemblyAnalyzer
open System
open System.Collections.Concurrent
open System.Diagnostics
open System.IO


let p = Run.styled
type Command =
    | Output_Path of string
    | Log_Level of LogLevel
with
    interface IArgParserTemplate with
        member _.Usage = ""

let args = ArgumentParser.Create(__SOURCE_FILE__).ParseCommandLine(Environment.GetCommandLineArgs().[1..])
args.TryGetResult <@ Log_Level @> |> Option.iter (fun l ->
    logLevel <- l
) 
if isDebug then printfn $"%A{Environment.GetCommandLineArgs()}"

let outputPath = args.GetResult <@ Output_Path @>
let resources = None

do
    String.Format(selectMessage resources (fun x -> x.startAnalysisHeader), p Styles.sourceLocation outputPath |> Run.markup)
    |> Run.ofMarkup
    |> Run.printLine

let watch = Stopwatch.StartNew()
let assemblyPaths = [
    yield! setBaseDir outputPath !!"LuaChecker*.dll"
    Path.Combine(outputPath, "server.dll")
]
if isDebug then printfn $"%A{assemblyPaths}"

let diagnostics = ConcurrentBag()
checkPublicUnusedMembers diagnostics assemblyPaths assemblyPaths
for d in diagnostics do Diagnostic.print resources d

let hasError = diagnostics |> Seq.exists (fun d -> Hint < d.severity)
do
    String.Format(selectMessage resources (fun x -> x.endAnalysis), p Styles.number $"{watch.Elapsed}" |> Run.markup)
    |> Run.ofMarkup
    |> Run.printLine

if hasError then
    exit -1
