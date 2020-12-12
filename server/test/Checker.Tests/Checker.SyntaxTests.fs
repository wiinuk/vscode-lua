module LuaChecker.Checker.SyntaxTests
open LuaChecker
open LuaChecker.TypeSystem
open LuaChecker.Checker.Test.Utils
open LuaChecker.Checker.Test.Helpers
open LuaChecker.Checker.Test.TypeExtensions
open Xunit
module C = Constraints
module S = Syntaxes
module T = TypedSyntaxes


[<Fact>]
let syntaxError() =
    chunkDiagnostics id "
    local function () end
    "
    =? [
        Syntax.ParseError.RequireAnyToken
        |> K.ParseError
        |> error (0, 0)
    ]
