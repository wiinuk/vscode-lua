
#nowarn "0025"
#nowarn "3186"
#r "nuget: FSharp.Data"
#r "nuget: Fake.Runtime"
#r "nuget: Fake.Api.GitHub"
#r "nuget: Fake.IO.FileSystem"
#r "nuget: Fake.Core.SemVer"
#r "nuget: Argu, version=5.1.0"
open Argu
open Fake.Api
open Fake.Core
open Fake.IO.Globbing.Operators
open Fake.Runtime
open FSharp.Data
open Octokit
open System


type Arguments =
    | [<AltCommandLine "-n">] UserName of string
    | [<AltCommandLine "-p">] Password of string
    | [<AltCommandLine "-r">] Repository of string
    | [<AltCommandLine "-t">] Token of string
with
    interface IArgParserTemplate with
        member _.Usage = ""

let args =
    let args = Environment.GetCommandLineArgs()
    let args =
        args
        |> Array.tryFindIndex ((=) "--")
        |> Option.map (fun i -> args.[i+1..])
        |> Option.defaultValue args

    ArgumentParser.Create(__SOURCE_FILE__).Parse args

let githubAuth =
    Environment.environVarOrNone "GITHUB_TOKEN"
    |> Option.orElseWith (fun _ ->
        args.TryGetResult <@ Token @>
    )
    |> Option.map (fun v ->
        Choice2Of2 {| token = v |}
    )
    |> Option.defaultWith (fun _ ->
        Choice1Of2 {| userName = args.GetResult <@ UserName @>; password = args.GetResult <@ Password @> |}
    )

let repository =
    Environment.environVarOrNone "GITHUB_REPOSITORY"
    |> Option.defaultWith (fun _ -> args.GetResult <@ Repository @>)
let [|owner; repositoryName|] = repository.Split([|'/'|], count = 2)


// 元の拡張ファイルを取得
let vsixPath = try !!"*.vsix" |> Seq.exactlyOne with _ -> eprintfn "*.vsix file is not found."; reraise()

// package.json からバージョンを取得
let packageInfo = JsonProvider<const(__SOURCE_DIRECTORY__ + "../../package.json")>.AsyncGetSample() |> Async.RunSynchronously
let newVersion = SemVer.parse packageInfo.Version
let newTagName = $"v{newVersion.NormalizeToShorter()}"
printfn $"Local tag name: {newTagName}"

// github の最新のリリースを取得
let github =
    match githubAuth with
    | Choice1Of2 p -> GitHub.createClient p.userName p.password
    | Choice2Of2 p -> GitHub.createClientWithToken p.token

let remoteRelease =
    try github |> GitHub.getLastRelease owner repositoryName |> Async.RunSynchronously |> Some
    with
    | :? NotFoundException -> None
    | :? AggregateException as e
        when e.InnerExceptions |> Seq.forall (fun x -> x :? NotFoundException)
        ->
        None

// 最新のリリースのバージョンと package.json のバージョンが同じなら終わる
// リリースするには明示的に package.json の version を変える必要がある
match remoteRelease with
| Some r when r.Release.TagName.Equals(newTagName, StringComparison.InvariantCultureIgnoreCase) ->
    printfn "It was not released. Increasing the version of package.json will release it."
    exit 0
| _ -> ()

// リリース
printfn $"Creating release: {owner} {repositoryName}, files: {vsixPath}"
github
    |> GitHub.draftNewRelease owner repositoryName newTagName newVersion.PreRelease.IsSome []
    |> GitHub.uploadFiles [vsixPath]
    |> GitHub.publishDraft
    |> Async.RunSynchronously
