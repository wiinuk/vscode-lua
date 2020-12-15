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
        normalizeMessages r =? normalizeMessages [
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
            "return require 'lib1'" &> ("C:/main.lua", 1)
            waitUntilHasDiagnosticsOf "file:///C:/main.lua"

            "return 123" &> ("C:/lib1.lua", 1)
            waitUntilMatchLatestDiagnosticsOf "file:///C:/main.lua" Array.isEmpty
        ]
        r =? [
            PublishDiagnostics {
                uri = "file:///C:/main.lua"
                diagnostics = [|
                    warning (0, 15) (0, 21) 1103 "ModuleNotFound(lib1, C:\lib1.lua)"
                |]
            }
            PublishDiagnostics { uri = "file:///C:/lib1.lua"; diagnostics = [||] }
            PublishDiagnostics { uri = "file:///C:/main.lua"; diagnostics = [||] }
        ]
    }
    [<Fact>]
    member _.didChangeError() = async {
        let! r = serverActions id [
            "return 1 + 1" &> ("C:/main.lua", 1)
            waitUntilHasDiagnosticsOf "file:///C:/main.lua"
            didChangeFull "return 1 .. 1" ("C:/main.lua", 2)
            waitUntilMatchLatestDiagnosticsOf "file:///C:/main.lua" (Array.isEmpty >> not)
        ]
        r =? [
            PublishDiagnostics { uri = "file:///C:/main.lua"; diagnostics = [||] }
            PublishDiagnostics {
                uri = "file:///C:/main.lua"
                diagnostics = [|
                    error (0, 7) (0, 8) 1004 "ConstraintMismatch(1.., ..string)"
                    error (0, 12) (0, 13) 1004 "ConstraintMismatch(1.., ..string)"
                |]
            }
        ]
    }
    [<Fact>]
    member _.hoverType() = async {
        let! r = serverActions id [
            "local x = 1 + 2" &> ("C:/main.lua", 1)
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
            PublishDiagnostics { uri = "file:///C:/main.lua"; diagnostics = [||] }
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
            "return 1 .. 2" &> ("C:/lib.lua", 1)
            waitUntilHasDiagnosticsOf "file:///C:/lib.lua"

            "local x = require 'lib'" &> ("C:/main.lua", 1)
            waitUntilHasDiagnosticsOf "file:///C:/main.lua"
        ]
        r =? [
            PublishDiagnostics {
                uri = "file:///C:/lib.lua"
                diagnostics = [|
                    error (0, 7) (0, 8) 1004 "ConstraintMismatch(1.., ..string)"
                    error (0, 12) (0, 13) 1004 "ConstraintMismatch(2.., ..string)"
                |]
            }
            PublishDiagnostics {
                uri = "file:///C:/main.lua"
                diagnostics = [|
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
                |]
            }
        ]
    }
    [<Fact>]
    member _.didChangeWatchedFiles() = async {
        let! r = serverActions id [
            "return 1 + 2" ?> "C:/lib.lua"
            Send <| DidChangeWatchedFiles {
                changes = [|
                    {
                        uri = Uri "file:///C:/lib.lua"
                        ``type`` = FileChangeType.Created
                    }
                |]
            }
            "local x = require 'lib'" &> ("C:/main.lua", 1)
            waitUntilHasDiagnosticsOf "file:///C:/main.lua"
        ]
        r =? [
            PublishDiagnostics {
                uri = "file:///C:/main.lua"
                diagnostics = [||]
            }
        ]
    }
    [<Fact>]
    member _.externalFileNoReply() = async {
        let files = [
            {| source = "return 1 + 2"; path = "C:/lib.lua" |}
        ]
        let! r = serverActions (fun c -> { c with initialFiles = files }) [
            "local x = require 'lib'" &> ("C:/main.lua", 1)
            waitUntilMatchLatestDiagnosticsOf "file:///C:/main.lua" Array.isEmpty
        ]
        removeOldDiagnostics r =? [
            PublishDiagnostics {
                uri = "file:///C:/main.lua"
                diagnostics = [||]
            }
        ]
    }
    [<Fact>]
    member _.externalFileEdit() = async {
        let files = [
            {| source = "return 1 + 2"; path = "C:/lib.lua" |}
        ]
        let! r = serverActions (fun c -> { c with initialFiles = files }) [
            "local x = require 'lib' .. 'a'" &> ("C:/main.lua", 1)
            waitUntilMatchLatestDiagnosticsOf "file:///C:/main.lua" (Array.isEmpty >> not)

            "return 'x'" ?> "C:/lib.lua"
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
            PublishDiagnostics {
                uri = "file:///C:/main.lua"
                diagnostics = [||]
            }
        ]
    }
    [<Fact>]
    member _.syntaxError() = async {
        let! r = serverActions id [
            "local = 1" &> ("C:/main.lua", 1)
            waitUntilHasDiagnosticsOf "file:///C:/main.lua"
        ]
        r =? [
            PublishDiagnostics {
                uri = "file:///C:/main.lua"
                diagnostics = [|
                    error (0, 6) (0, 7) 0007 "RequireName"
                |]
            }
        ]
    }
