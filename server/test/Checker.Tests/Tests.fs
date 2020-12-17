module LuaChecker.Tests
open LuaChecker.Checker.Test.Utils
open System
open Xunit


[<Fact>]
let escapedPath() =
    let localPath =
        Uri "file:///c%3A/dir/file.ext"
        |> DocumentPath.ofUri
        |> DocumentPath.toPathOrFail

    if Environment.OSVersion.Platform = PlatformID.Win32NT then
        localPath =? "c:\\dir\\file.ext"
    else
        localPath =? "/c:/dir/file.ext"
