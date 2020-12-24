namespace LuaChecker.Server
open FsCheck
open FsCheck.Xunit
open LuaChecker
open LuaChecker.Server.Protocol
open LuaChecker.Server.Test.Helpers
open LuaChecker.Test
open LuaChecker.Text.Json
open System
open System.Text
open global.Xunit
open Xunit.Abstractions
open type Marshalling.KnownSemanticTokenModifiers
open type Marshalling.KnownSemanticTokenTypes


type Tests(fixture: TestsFixture, output: ITestOutputHelper) =
    let t x1 x2 x3 x4 x5 = [|x1; x2; x3; int x4; int x5|]
    let data xss = [| for xs in xss do yield! xs |]
    let async = ExtraTopLevelOperators.async

    do fixture.SetOutput output
    interface TestsFixture IClassFixture

    [<Property>]
    member _.blockingStream inputs (PositiveInt bufferSize) = Async.RunSynchronously <| async {
        let utf8 = Encoding.UTF8
        let stream = new BlockingStream(ReadTimeout = 1000, WriteTimeout = 1000)
        let outputs = ResizeArray()
        let read = async {
            let buffer = Array.zeroCreate (max 1 bufferSize)
            while
                let readLength = stream.Read(buffer, 0, buffer.Length) in

                (if readLength < 0 then failwithf "readLength: %d < 0" readLength);
                (if buffer.Length < readLength then failwithf "b.Length < readLength: %d" readLength);

                outputs.AddRange(Seq.take readLength buffer);

                buffer.Length = readLength
                do ()

            stream.Close()
        }
        let write = async {
            inputs
            |> List.iter (fun (NonNull input) ->
                let input = utf8.GetBytes(s = input)
                stream.Write(input, 0, input.Length)
            )
            stream.CompleteWriting()
        }
        let! _units = Async.Parallel [read; write]
        return String.concat "" [for NonNull x in inputs -> x ] =? utf8.GetString(outputs.ToArray())
    }
    [<Fact>]
    member _.initializeAndExit() = async {
        let! r = serverActionsWithBoilerPlate id [
            Send <| Initialize { rootUri = ValueSome(Uri "file:///") }
            Send Initialized
            receiveRequest 5.<_> <| function RegisterCapability _ -> Some RegisterCapabilityResponse | _ -> None
            Send Shutdown
            waitUntilExists 5.<_> <| function ShutdownResponse -> true | _ -> false
            Send Exit
        ]
        r =? normalizeMessages [
            InitializeResponse {
                capabilities = {
                    hoverProvider = true
                    textDocumentSync = {
                        openClose = true
                        save = Defined { includeText = false }
                        change = TextDocumentSyncKind.Incremental
                    }
                    semanticTokensProvider = Defined {
                        legend = {
                            tokenTypes = [|
                                "namespace"; "type"; "class"; "enum"; "interface";
                                "struct"; "typeParameter"; "parameter"; "variable"; "property";
                                "enumMember"; "event"; "function"; "method"; "macro";
                                "keyword"; "modifier"; "comment"; "string"; "number";
                                "regexp"; "operator"
                            |]
                            tokenModifiers = [|
                                "declaration"; "definition"; "readonly"; "static"; "deprecated";
                                "abstract"; "async"; "modification"; "documentation"; "defaultLibrary"
                            |]
                        }
                        range = Defined true
                        full = Defined {
                            delta = Defined false
                        }
                    }
                }
            }
            RegisterCapability {
                registrations = [|
                    {
                        id = "ba98ad6e-1d88-493e-ae0c-4c6f56d69ada"
                        methodAndRegisterOptions = RegisterOptions.DidChangeWatchedFiles {
                            watchers = [|
                                {
                                    globPattern = "**/*.lua"
                                    kind = Undefined
                                }
                            |]
                        }
                    }
                |]
            }
            ShutdownResponse
        ]
    }
    [<Fact>]
    member _.didOpen2() = async {
        let! r = serverActions id [
            "return require 'lib1'" &> ("file:///C:/main.lua", 1)
            waitUntilHasDiagnosticsOf "file:///C:/main.lua"

            "return 123" &> ("file:///C:/lib1.lua", 1)
            waitUntilMatchLatestDiagnosticsOf "file:///C:/main.lua" Array.isEmpty
        ]
        sortDiagnosticsAndOthers r =? ([
            publishDiagnostics "file:///C:/main.lua" 1 [
                warning (0, 15) (0, 21) 1103 "ModuleNotFound(lib1, C:\lib1.lua)"
            ]
            publishDiagnostics "file:///C:/lib1.lua" 2 []
            publishDiagnostics "file:///C:/main.lua" 3 []
        ], [])
    }
    [<Fact>]
    member _.didChangeError() = async {
        let! r = serverActions id [
            "return 1 + 1" &> ("file:///C:/main.lua", 1)
            waitUntilHasDiagnosticsOf "file:///C:/main.lua"
            didChangeFull "return 1 .. 1" ("file:///C:/main.lua", 2)
            waitUntilMatchLatestDiagnosticsOf "file:///C:/main.lua" (Array.isEmpty >> not)
        ]
        sortDiagnosticsAndOthers r =? ([
            publishDiagnostics "file:///C:/main.lua" 1 []
            publishDiagnostics "file:///C:/main.lua" 2 [
                error (0, 7) (0, 8) 1004 "ConstraintMismatch(1.., ..string)"
                error (0, 12) (0, 13) 1004 "ConstraintMismatch(1.., ..string)"
            ]
        ], [])
    }
    [<Fact>]
    member _.hoverType() = async {
        let! r = serverActions id [
            "local x = 1 + 2" &> ("file:///C:/main.lua", 1)
            waitUntilHasDiagnosticsOf "file:///C:/main.lua"

            Send <| Hover {
                textDocument = { uri = Uri "file:///C:/main.lua" }
                position = { line = 0; character = 6 }
            }
            waitUntilExists 5.<_> <| function
                | HoverResponse _ -> true
                | _ -> false
        ]
        r =? [
            publishDiagnostics "file:///C:/main.lua" 1 []
            {
                contents = {
                    kind = MarkupKind.markdown
                    value = String.concat "\n" [
                        "```lua"
                        "---@generic x: number.."
                        "local x: x"
                        "```"
                    ]
                }
                range = Undefined
            }
            |> ValueSome
            |> HoverResponse
        ]
    }
    [<Fact>]
    member _.externalModuleErrorMessage() = async {
        let! r = serverActions id [
            "return 1 .. 2" &> ("file:///C:/lib.lua", 1)
            waitUntilHasDiagnosticsOf "file:///C:/lib.lua"

            "local x = require 'lib'" &> ("file:///C:/main.lua", 1)
            waitUntilHasDiagnosticsOf "file:///C:/main.lua"
        ]
        sortDiagnosticsAndOthers r =? ([
            publishDiagnostics "file:///C:/lib.lua" 1 [
                error (0, 7) (0, 8) 1004 "ConstraintMismatch(1.., ..string)"
                error (0, 12) (0, 13) 1004 "ConstraintMismatch(2.., ..string)"
            ]
            publishDiagnostics "file:///C:/main.lua" 2 [
                { error (0, 18) (0, 23) 1104 "ExternalModuleError(C:\\lib.lua, (1,8 - 1,9) Error: ConstraintMismatch(1.., ..string))" with
                    relatedInformation = Defined [|
                        {
                            location = {
                                uri = "file:///C:/lib.lua"
                                range = range (0, 7) (0, 8)
                            }
                            message = "ConstraintMismatch(1.., ..string)"
                        }
                    |]
                }
            ]
        ], [])
    }
    [<Fact>]
    member _.didChangeWatchedFiles() = async {
        let! r = serverActions id [
            "return 1 + 2" ?> "file:///C:/lib.lua"
            Send <| DidChangeWatchedFiles {
                changes = [|
                    {
                        uri = Uri "file:///C:/lib.lua"
                        ``type`` = FileChangeType.Created
                    }
                |]
            }
            "local x = require 'lib'" &> ("file:///C:/main.lua", 1)
            waitUntilMatchLatestDiagnosticsOf "file:///C:/main.lua" Array.isEmpty
        ]
        removeOldDiagnostics r =? [
            PublishDiagnostics <| publishDiagnosticsParams "file:///C:/main.lua" []
        ]
    }
    [<Fact>]
    member _.externalFileNoReply() = async {
        let files = [
            {| source = "return 1 + 2"; uri = "file:///C:/lib.lua" |}
        ]
        let! r = serverActions (fun c -> { c with initialFiles = files }) [
            "local x = require 'lib'" &> ("file:///C:/main.lua", 1)
            waitUntilMatchLatestDiagnosticsOf "file:///C:/main.lua" Array.isEmpty
        ]
        removeOldDiagnostics r =? [
            PublishDiagnostics <| publishDiagnosticsParams "file:///C:/main.lua" []
        ]
    }
    [<Fact>]
    member _.externalFileEdit() = async {
        let files = [
            {| source = "return 1 + 2"; uri = "file:///C:/lib.lua" |}
        ]
        let! r = serverActions (fun c -> { c with initialFiles = files }) [
            "local x = require 'lib' .. 'a'" &> ("file:///C:/main.lua", 1)
            waitUntilMatchLatestDiagnosticsOf "file:///C:/main.lua" (Array.isEmpty >> not)

            "return 'x'" ?> "file:///C:/lib.lua"
            Send <| DidChangeWatchedFiles {
                changes = [|
                    {
                        uri = Uri "file:///C:/lib.lua"
                        ``type`` = FileChangeType.Changed
                    }
                |]
            }
            waitUntilMatchLatestDiagnosticsOf "file:///C:/main.lua" Array.isEmpty
        ]
        removeOldDiagnostics r =? [
            PublishDiagnostics <| publishDiagnosticsParams "file:///C:/main.lua" []
        ]
    }
    [<Fact>]
    member _.syntaxError() = async {
        let! r = serverActions id [
            "local = 1" &> ("file:///C:/main.lua", 1)
            waitUntilHasDiagnosticsOf "file:///C:/main.lua"
        ]
        r =? [
            publishDiagnostics "file:///C:/main.lua" 1 [
                error (0, 6) (0, 7) 0007 "RequireName"
            ]
        ]
    }
    [<Fact>]
    member _.customGlobalModule() = async {
        let withConfig c =
            { c with
                globalModuleFiles = [
                    {|
                    path = "/system/custom-standard.d.lua"
                    source = "---@global MyVariable string"
                    |}
                ]
                rootUri = Uri "file:///project"
            }
        let! r = serverActions withConfig [
            "return MyVariable" &> ("file:///project/main.lua", 1)
            waitUntilHasDiagnosticsOf "file:///project/main.lua"
        ]
        r =? [
            publishDiagnostics "file:///project/main.lua" 1 []
        ]
    }
    [<Fact>]
    member _.encodedUri() = async {
        let! r = serverActions (fun c -> { c with rootUri = Uri "file:///c%3A/" }) [
            "local x = 10" &> ("file:///c%3A/main.lua", 1)
            waitUntilHasDiagnosticsOf "file:///c:/main.lua"
        ]
        r =? [
            publishDiagnostics "file:///c:/main.lua" 1 []
        ]
    }
    [<Fact>]
    member _.semanticTokenFull() = async {
        let! r = semanticTokenFullResponseData "local x = 10"
        r =? data [
            t 0 6 1 number definition
            t 0 4 2 number Empty
        ]
    }
    [<Fact>]
    member _.semanticTokenRange() = async {
        let! r = serverActions id [
            "local x = 10\nlocal y = 'test'" &> ("file:///main.lua", 1)
            waitUntilHasDiagnosticsOf "file:///main.lua"
            Send <| SemanticTokensRange {
                SemanticTokensRangeParams.textDocument = { uri = Uri "file:///main.lua" }
                range = {
                    start = { line = 1; character = 0 }
                    ``end`` = { line = 1; character = 15 }
                }
            }
            waitUntilExists 5.<_> <| function
                | SemanticTokensRangeResponse _ -> true
                | _ -> false
        ]
        r =? [
            publishDiagnostics "file:///main.lua" 1 []
            SemanticTokensRangeResponse <| ValueSome {
                resultId = Undefined
                data = data [
                    t 1 6 1 string definition
                    t 0 4 6 string Empty
                ]
            }
        ]
    }
    [<Fact>]
    member _.semanticTokenFunctionAndInterface() = async {
        let! r = semanticTokenFullResponseData "local function localFunction(table) return table.field end"
        r =? data [
            t 0 15 13 ``function`` definition
            t 0 14 5 parameter definition
            t 0 14 5 parameter Empty
            t 0 6 5 property Empty
        ]
    }
    [<Fact>]
    member _.semanticTokenTypeTag() = async {
        let! r = semanticTokenFullResponseData "local x = --[[---@type string]](10)"
        r =? data [
            t 0 6 1 string definition
            t 0 11 1 keyword Empty
            t 0 1 4 keyword Empty
            t 0 5 6 ``type`` Empty
            t 0 9 2 number Empty
        ]
    }
    [<Fact>]
    member _.semanticTokenGlobalTag() = async {
        let! r = semanticTokenFullResponseData "---@global myNumber number"
        r =? data [
            t 0 3 1 keyword Empty
            t 0 1 6 keyword Empty
            t 0 7 8 number declaration
            t 0 9 6 ``type`` Empty
        ]
    }
    [<Fact>]
    member _.semanticTokenGenericType() = async {
        let! r = semanticTokenFullResponseData "---@global myTable table<string, number>"
        r =? data [
            t 0 3 1 keyword Empty
            t 0 1 6 keyword Empty
            t 0 7 7 variable declaration
            t 0 8 5 ``type`` Empty
            t 0 5 1 operator Empty
            t 0 1 6 ``type`` Empty
            t 0 6 1 operator Empty
            t 0 2 6 ``type`` Empty
            t 0 6 1 operator Empty
        ]
    }
    [<Fact>]
    member _.semanticTokenBeforeStatement() = async {
        let! r = semanticTokenFullResponseData "---@global x number\nlocal a = 0"
        r =? data [
            t 0 3 1 keyword Empty
            t 0 1 6 keyword Empty
            t 0 7 1 number declaration
            t 0 2 6 ``type`` Empty
            t 1 6 1 number definition
            t 0 4 1 number Empty
        ]
    }
    [<Fact>]
    member _.semanticTokenAfterStatement() = async {
        let! r = semanticTokenFullResponseData "local a = 0\n---@global x number"
        r =? data [
            t 0 6 1 number definition
            t 0 4 1 number Empty
            t 1 3 1 keyword Empty
            t 0 1 6 keyword Empty
            t 0 7 1 number declaration
            t 0 2 6 ``type`` Empty
        ]
    }
    [<Fact>]
    member _.semanticTokenFeatureTag() = async {
        let! r = semanticTokenFullResponseData "---@_Feature require\n---@global myRequire any"
        r =? data [
            t 0 3 1 keyword Empty
            t 0 1 8 keyword Empty
            t 0 9 7 keyword Empty
            t 1 3 1 keyword Empty
            t 0 1 6 keyword Empty
            t 0 7 9 variable declaration
            t 0 10 3 keyword Empty
        ]
    }
    [<Fact>]
    member _.semanticTokenGlobalTagWithGenericTag2() = async {
        let! r = semanticTokenFullResponseData "---@generic a\n---@generic b\n---@global myFunction fun(a, b): ()"
        r =? data [
            t 0 3 1 keyword Empty
            t 0 1 7 keyword Empty
            t 0 8 1 typeParameter definition
            t 1 3 1 keyword Empty
            t 0 1 7 keyword Empty
            t 0 8 1 typeParameter definition
            t 1 3 1 keyword Empty
            t 0 1 6 keyword Empty
            t 0 7 10 ``function`` declaration
            t 0 11 3 keyword Empty
            t 0 3 1 operator Empty
            t 0 1 1 ``type`` Empty
            t 0 1 1 operator Empty
            t 0 2 1 ``type`` Empty
            t 0 1 1 operator Empty
            t 0 1 1 operator Empty
            t 0 2 1 operator Empty
            t 0 1 1 operator Empty
        ]
    }
    [<Fact>]
    member _.semanticTokenTypeTagWithGenericTag2() = async {
        let! r = semanticTokenFullResponseData "local x = --[[---@generic a\n---@generic b\n---@type fun(a, b): ()]](42)"
        r =? data [
            t 0 6 1 ``function`` definition
            t 0 11 1 keyword Empty
            t 0 1 7 keyword Empty
            t 0 8 1 typeParameter definition
            t 1 3 1 keyword Empty
            t 0 1 7 keyword Empty
            t 0 8 1 typeParameter definition
            t 1 3 1 keyword Empty
            t 0 1 4 keyword Empty
            t 0 5 3 keyword Empty
            t 0 3 1 operator Empty
            t 0 1 1 ``type`` Empty
            t 0 1 1 operator Empty
            t 0 2 1 ``type`` Empty
            t 0 1 1 operator Empty
            t 0 1 1 operator Empty
            t 0 2 1 operator Empty
            t 0 1 1 operator Empty
            t 0 4 2 number Empty
        ]
    }
    [<Fact>]
    member _.semanticTokenClassTagWithGenericTag2() = async {
        let! r = semanticTokenFullResponseData "---@generic arg1\n---@generic arg2\n---@class MyFunction : fun(arg1, arg2) : ()"
        r =? data [
            t 0 3 1 keyword Empty
            t 0 1 7 keyword Empty
            t 0 8 4 typeParameter definition
            t 1 3 1 keyword Empty
            t 0 1 7 keyword Empty
            t 0 8 4 typeParameter definition
            t 1 3 1 keyword Empty
            t 0 1 5 keyword Empty
            t 0 6 10 ``function`` Empty
            t 0 11 1 operator Empty
            t 0 2 3 keyword Empty
            t 0 3 1 operator Empty
            t 0 1 4 ``type`` Empty
            t 0 4 1 operator Empty
            t 0 2 4 ``type`` Empty
            t 0 4 1 operator Empty
            t 0 2 1 operator Empty
            t 0 2 1 operator Empty
            t 0 1 1 operator Empty
        ]
    }
