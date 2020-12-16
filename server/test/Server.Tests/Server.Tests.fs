namespace LuaChecker.Server
open FsCheck
open FsCheck.Xunit
open LuaChecker
open LuaChecker.Server.Log
open LuaChecker.Server.Protocol
open LuaChecker.Server.Test.Helpers
open LuaChecker.Text.Json
open System
open System.Text
open global.Xunit
open Xunit.Abstractions


type TestsFixture() =
    let mutable outputLogger = None

    member _.SetupOutput(output: ITestOutputHelper) =
        match outputLogger with
        | None ->
            let logger = { new Logger() with
                member _.Log e = output.WriteLine("[{0:O}] {1} : {2} : {3}", e.time, e.source, e.level, e.message)
            }
            outputLogger <- Some logger
            Logger.add Log.logger logger

        | _ -> ()

    interface IDisposable with
        member _.Dispose() =
            outputLogger |> Option.iter (Logger.remove Log.logger)

type Tests(fixture: TestsFixture, output: ITestOutputHelper) =
    do fixture.SetupOutput output
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
        r =? [
            publishDiagnostics "file:///C:/main.lua" 1 [
                warning (0, 15) (0, 21) 1103 "ModuleNotFound(lib1, C:\lib1.lua)"
            ]
            publishDiagnostics "file:///C:/lib1.lua" 2 []
            publishDiagnostics "file:///C:/main.lua" 3 []
        ]
    }
    [<Fact>]
    member _.didChangeError() = async {
        let! r = serverActions id [
            "return 1 + 1" &> ("file:///C:/main.lua", 1)
            waitUntilHasDiagnosticsOf "file:///C:/main.lua"
            didChangeFull "return 1 .. 1" ("file:///C:/main.lua", 2)
            waitUntilMatchLatestDiagnosticsOf "file:///C:/main.lua" (Array.isEmpty >> not)
        ]
        sortDiagnosticsOrFail r =? [
            publishDiagnostics "file:///C:/main.lua" 1 []
            publishDiagnostics "file:///C:/main.lua" 2 [
                error (0, 7) (0, 8) 1004 "ConstraintMismatch(1.., ..string)"
                error (0, 12) (0, 13) 1004 "ConstraintMismatch(1.., ..string)"
            ]
        ]
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
                        "x: x"
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
        sortDiagnosticsOrFail r =? [
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
        ]
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
        r =? [
            publishDiagnostics "file:///C:/main.lua" 1 []
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
        r =? [
            publishDiagnostics "file:///C:/main.lua" 1 [
                warning (0, 18) (0, 23) 1103 "ModuleNotFound(lib, C:\lib.lua)"
            ]
            publishDiagnostics "file:///C:/main.lua" 2 []
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
            publishDiagnostics "file:///C:/main.lua" 2 []
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
