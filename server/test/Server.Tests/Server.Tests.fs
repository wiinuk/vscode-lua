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
type private T = Marshalling.KnownSemanticTokenTypes
type private M = Marshalling.KnownSemanticTokenModifiers


type Tests(fixture: TestsFixture, output: ITestOutputHelper) =
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
        let! r = serverActions id [
            "local x = 10" &> ("file:///main.lua", 1)
            waitUntilHasDiagnosticsOf "file:///main.lua"
            Send <| SemanticTokensFull { SemanticTokensParams.textDocument = { uri = Uri "file:///main.lua" } }
            waitUntilExists 5.<_> <| function
                | SemanticTokensFullResponse _ -> true
                | _ -> false
        ]
        r =? [
            publishDiagnostics "file:///main.lua" 1 []
            SemanticTokensFullResponse <| ValueSome {
                resultId = Undefined
                data = [|
                    0; 6; 1; int T.number; int M.Empty;
                    0; 4; 2; int T.number; int M.Empty;
                |]
            }
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
                data = [|
                    1; 6; 1; int T.string; int M.Empty;
                    0; 4; 6; int T.string; int M.Empty;
                |]
            }
        ]
    }
    [<Fact>]
    member _.semanticTokenFunctionAndInterface() = async {
        let! r = serverActions id [
            "local function localFunction(table) return table.field end" &> ("file:///main.lua", 1)
            waitUntilHasDiagnosticsOf "file:///main.lua"
            Send <| SemanticTokensFull { SemanticTokensParams.textDocument = { uri = Uri "file:///main.lua" } }
            waitUntilExists 5.<_> <| function
                | SemanticTokensFullResponse _ -> true
                | _ -> false
        ]
        r =? [
            publishDiagnostics "file:///main.lua" 1 []
            SemanticTokensFullResponse <| ValueSome {
                resultId = Undefined
                data = [|
                    0; 15; 13; int T.``function``; int M.Empty;
                    0; 14; 5; int T.parameter; int M.definition;
                    0; 14; 5; int T.parameter; int M.Empty;
                    0; 6; 5; int T.property; int M.Empty;
                |]
            }
        ]
    }
