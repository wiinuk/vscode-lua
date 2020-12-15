module LuaChecker.Checker.ModuleTests
open Xunit
open LuaChecker
open LuaChecker.TypeSystem
open LuaChecker.Checker.Test.Utils
open LuaChecker.Checker.Test.TypeExtensions
open LuaChecker.Checker.Test.Helpers
open LuaChecker.Primitives
type private K = LuaChecker.DiagnosticKind


[<Fact>]
let indirectModuleRequire() =
    projectSchemes id [
        "return require('lib1')" &> "C:/main.lua"
        "return require('framework1')" &> "C:/lib1.lua"
        "return 'aaa'" &> "C:/framework1.lua"
        Check "C:/main.lua"
    ] =? [
        Ok(type0 types.string)
    ]

[<Fact>]
let moduleNotFound() =
    projectSchemes id [
        "return require('lib1')" &> "C:/main.lua"
        Check "C:/main.lua"
    ] =? [
        Error [
            warning (15, 21) <| K.ModuleNotFound("lib1", [toDocumentPath "C:/lib1.lua"])
        ]
    ]

[<Fact>]
let errorFromExternalModule() =
    projectSchemes id [
        "return 'aa' + 'bb'" &> "C:/lib1.lua"
        "return require('lib1')" &> "C:/main.lua"
        Check "C:/main.lua"
    ] =? [
        Error [
            error (15, 21) <| K.ExternalModuleError(
                toDocumentPath "C:/lib1.lua",
                error (7, 11) <| K.UnifyError(ConstraintMismatch(Constraints.stringOrUpper "aa", Constraints.tagOrLower TagSpace.allNumber))
            )
        ]
    ]

[<Fact>]
let latestExternalModule() =
    projectSchemes id [
        "return 'aa'" &> "C:/lib1.lua"
        "return require('lib1')" &> "C:/main.lua"
        "return 123" &> "C:/lib1.lua"
        Check "C:/main.lua"
    ] =? [
        Ok(type0 types.number)
    ]

[<Fact>]
let externalModuleUpdate() =
    projectSchemes id [
        "return 'aa'" &> "C:/lib1.lua"
        "return require('lib1')" &> "C:/main.lua"
        Check "C:/main.lua"
        "return 123" &> "C:/lib1.lua"
        Check "C:/main.lua"
    ] =? [
        Ok(type0 types.string)
        Ok(type0 types.number)
    ]

[<Fact>]
let removedModuleError() =
    projectSchemes id [
        "return 'aa'" &> "C:/lib1.lua"
        "return require('lib1')" &> "C:/main.lua"
        Check "C:/main.lua"
        Remove "C:/lib1.lua"
        Check "C:/main.lua"
    ] =? [
        Ok(type0 types.string)
        Error [
            warning (15, 21) <| K.ModuleNotFound("lib1", [toDocumentPath "C:/lib1.lua"])
        ]
    ]

[<Fact>]
let selfRecursionModuleError() =
    // lib1 -> lib1
    projectSchemes id [
        "return require 'lib1'" &> "C:/lib1.lua"
        Check "C:/lib1.lua"
    ] =? [
        Error [
            warning (15, 21) <| K.RecursiveModuleReference(toDocumentPath "C:/lib1.lua")
        ]
    ]

[<Fact>]
let mutualRecursionModuleError() =
    // lib1 -> lib2
    // lib2 -> lib1
    projectSchemes id [
        "return require 'lib2'" &> "C:/lib1.lua"
        "return require 'lib1' + 1" &> "C:/lib2.lua"
        Check "C:/lib1.lua"
    ] =? [
        Error [
            warning (15, 21) (
                K.ExternalModuleError(
                    toDocumentPath "C:/lib2.lua",
                    warning (15, 21) <| K.RecursiveModuleReference(toDocumentPath "C:/lib1.lua")
                )
            )
        ]
    ]

[<Fact>]
let doubleReference() =
    // lib1 -> lib2
    // main -> lib2
    // main -> lib1
    projectSchemes id [
        "return require 'lib1' + require 'lib2'" &> "C:/main.lua"
        "return require 'lib2'" &> "C:/lib1.lua"
        "return 123" &> "C:/lib2.lua"
        Check "C:/main.lua"
    ] =? [
        Ok(type0 types.number)
    ]

[<Fact>]
let isAncestor() =
    //                   ┌──────┐
    // [main] → [lib1] → │ lib3 │
    //          [lib2] → │      │
    //                   └──────┘
    projectActionsToScheme id [
        "require 'lib1'" &> "main"
        "require 'lib3'" &> "lib1"
        "require 'lib3'" &> "lib2"
        "" &> "lib3"
        Check "main"
        Check "lib2"

        IsAncestor("main", "main")
        IsAncestor("lib1", "main")
        IsAncestor("lib2", "main")
        IsAncestor("lib3", "main")

        IsAncestor("main", "lib1")
        IsAncestor("lib1", "lib1")
        IsAncestor("lib2", "lib1")
        IsAncestor("lib3", "lib1")

        IsAncestor("main", "lib2")
        IsAncestor("lib1", "lib2")
        IsAncestor("lib2", "lib2")
        IsAncestor("lib3", "lib2")

        IsAncestor("main", "lib3")
        IsAncestor("lib1", "lib3")
        IsAncestor("lib2", "lib3")
        IsAncestor("lib3", "lib3")
    ] =? [
        CheckResult(Ok(type0 types.nil))
        CheckResult(Ok(type0 types.nil))

        IsAncestorResult false
        IsAncestorResult true
        IsAncestorResult false
        IsAncestorResult true

        IsAncestorResult false
        IsAncestorResult false
        IsAncestorResult false
        IsAncestorResult true

        IsAncestorResult false
        IsAncestorResult false
        IsAncestorResult false
        IsAncestorResult true

        IsAncestorResult false
        IsAncestorResult false
        IsAncestorResult false
        IsAncestorResult false
    ]

[<Fact>]
let parseAndCheck() =
    projectSchemes id [
        "return require 'lib1'" &>< ("main", 1)
        "return 123" &>< ("lib1", 1)
        Check "main"
    ] =? [
        Error [
            warning (15, 21) <| K.ModuleNotFound("lib1", [toDocumentPath "C:\lib1.lua"])
        ]
        Ok types.number
        Ok types.number
    ]

[<Fact>]
let caseInsensitiveModuleResolve() =
    projectSchemes id [
        "return 'ok'" &> "LIB1"
        "return require 'lib1'" &> "main"
        Check "main"
    ] =? [
        Ok types.string
    ]

[<Fact>]
let caseSensitiveModuleResolve() =
    projectSchemes (fun c -> { c with caseSensitiveModuleResolve = true }) [
        "return 'ok'" &> "LIB1"
        "return require 'lib1'" &> "main"
        Check "main"
    ] =? [
        Error [
            warning (15, 21) <| K.ModuleNotFound("lib1", [toDocumentPath "C:\lib1.lua"])
        ]
    ]

[<Fact>]
let resolveModuleNameWithDot() =
    projectSchemes id [
        "return 'ok'" &> "C:/lib1/ver2.lua"
        "return require 'lib1.ver2'" &> "C:/main.lua"
        Check "main"
    ] =? [
        Ok <| type0 types.string
    ]

[<Fact>]
let resolveModuleNameWithDotFailure() =
    projectSchemes id [
        "return 'ok'" &> "C:/lib1.ver2.lua"
        "return require 'lib1.ver2'" &> "C:/main.lua"
        Check "main"
    ] =? [
        Error [
            warning (15, 26) <| K.ModuleNotFound("lib1.ver2", [toDocumentPath "C:/lib1/ver2.lua"])
        ]
    ]

[<Fact>]
let packagePath() =
    projectSchemes id [
        "return 'ok'" &> "C:/libraries/lib1.lua"
        "
        package.path = package.path..';./libraries/?.lua'
        return require 'lib1'
        " &> "C:/main.lua"
        Check "main"
    ] =? [
        Ok <| type0 types.string
    ]

[<Fact>]
let packagePathPrecedence() =
    projectSchemes id [
        "return 123" &> "C:/libraries/lib1.lua"
        "return 'ok'" &> "C:/lib1.lua"
        "
        package.path = package.path..';./libraries/?.lua'
        return require 'lib1'
        " &> "C:/main.lua"
        Check "main"
    ] =? [
        Ok <| type0 types.string
    ]

[<Fact>]
let packagePathPrecedence2() =
    projectSchemes id [
        "return 123" &> "C:/libraries/lib1.lua"
        "return 'ok'" &> "C:/lib1.lua"
        "
        package.path = './libraries/?.lua;'..package.path
        return require 'lib1'
        " &> "C:/main.lua"
        Check "main"
    ] =? [
        Ok <| type0 types.number
    ]

[<Fact>]
let updateCheck() =
    projectSchemes id [
        "return 'a' .. 'b'" &>< ("main", 1)
        "return 'a' + 'b'" &>< ("main", 2)
    ] =? [
        Ok <| type0 types.string
        Error [
            error (7, 10) <| K.UnifyError(ConstraintMismatch(Constraints.stringOrUpper "a", Constraints.tagOrLower TagSpace.allNumber))
            error (13, 16) <| K.UnifyError(ConstraintMismatch(Constraints.stringOrUpper "b", Constraints.tagOrLower TagSpace.allNumber))
        ]
    ]

[<Fact>]
let additionalEnvironments() =
    projectSchemeAndDiagnostics id [
        "
        ---@global Lib1State string
        Lib1State = 'ready'
        " &> "lib1"
        "
        local _ = Lib1State
        require 'lib1'
        return Lib1State
        " &> "main"

        Check "main"
    ]
    =? [
        Scheme.normalize types.string, [
            error (19, 28) <| K.NameNotFound "Lib1State"
        ]
    ]

[<Fact>]
let parentModuleGlobal() =
    projectSchemeAndDiagnostics id [
        "
        ---@global Lib1Counter number
        Lib1Counter = 42
        " &> "lib1"
        "
        local function f()
            require 'lib1'
            local s = Lib1Counter
        end
        return Lib1Counter
        " &> "main"
        Check "main"
    ]
    =? [
        types.number, [
            warning (48, 54) <| K.UndeterminedGlobalVariableEnvironment(toDocumentPath "lib1", Map [
                "Lib1Counter", NonEmptyList(
                    {
                        scheme = types.number
                        declarationKind = DeclarationKind.NoFeatures
                        location = Some <| Location(toDocumentPath "lib1", { start = 20; end' = 31 })
                    },
                    []
                )
            ])
        ]
    ]

[<Fact>]
let ancestorsModuleGlobal() =
    projectSchemeAndDiagnostics id [
        "
        ---@global Lib1State string
        Lib1State = 'ready'
        " &> "lib1"
        "
        ---@global Lib2Counter number
        Lib2Counter = 42
        " &> "lib2"
        "
        require 'lib1'
        require 'lib2'
        " &> "lib3"
        "
        require 'lib3'

        local s = Lib1State
        local s = Lib2Counter
        " &> "main"

        Check "main"
    ]
    =? [
        Scheme.normalize types.nil, []
    ]

[<Fact>]
let collisionGlobal() =
    projectSchemeAndDiagnostics id [
        "
        ---@global Id string
        Id = 'abc'
        ---@global Lucky boolean
        Lucky = true
        " &> "lib1"
        "
        ---@global Id number
        Id = 123
        ---@global Lucky boolean
        Lucky = true
        " &> "lib2"
        "
        require 'lib1'
        require 'lib2'

        local x = Id
        local x = Lucky
        " &> "main"

        Check "main"
    ] =? [
        Scheme.normalize types.nil, [
            error (66, 68) <| K.GlobalNameCollision(
                "Id",
                {
                    scheme = types.string
                    declarationKind = DeclarationKind.NoFeatures
                    location = Some <| Location(toDocumentPath "lib1", { start = 20; end' = 22 })
                },
                {
                    scheme = types.number
                    declarationKind = DeclarationKind.NoFeatures
                    location = Some <| Location(toDocumentPath "lib2", { start = 20; end' = 22 })
                },
                []
            )
        ]
    ]

[<Fact(DisplayName = "---@_Feature require")>]
let globalDeclWithFeature() =
    projectSchemes id [
        "return 123" &> "lib1"
        "
        ---@_Feature require
        ---@global myRequire _

        return myRequire 'lib1'
        " &> "main"

        Check "main"
    ] =? [
        Ok types.number
    ]
