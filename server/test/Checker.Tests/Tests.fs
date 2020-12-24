module LuaChecker.Tests
open LuaChecker.Checker.Test.Utils
open LuaChecker.Test
open System
open Xunit


[<Fact>]
let escapedPath() =
    Uri "file:///c%3A/dir/file.ext"
    |> DocumentPath.ofUri
    |> DocumentPath.toPathOrFail
    =? "c:\\dir\\file.ext"
