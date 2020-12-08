module LuaChecker.Server.Tests
open FsCheck
open FsCheck.Xunit
open LuaChecker
open LuaChecker.Server.Protocol
open LuaChecker.Server.Test.Helpers
open LuaChecker.Text.Json
open System
open System.Text
open global.Xunit


let [<Property>] blockingStream inputs (PositiveInt bufferSize) = Async.RunSynchronously <| async {
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
let [<Fact>] initializeAndExit() = async {
    let! r = serverActionsWithBoilerPlate id [
        Send <| Initialize { rootUri = ValueSome(Uri "file:///") }
        Send Initialized
        Send Shutdown
        Send Exit
    ]
    r =? [
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
        ShutdownResponse
    ]
}
let [<Fact>] didOpen2() = async {
    let! r = serverActions id [
        "return require 'lib1'" &> ("C:/main.lua", 1)
        "return 123" &> ("C:/lib1.lua", 1)
        WhenMessages(List.length >> (<=) 4, Some <| TimeSpan.FromSeconds 5.)
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
let [<Fact>] didChangeError() = async {
    let! r = serverActions id [
        "return 1 + 1" &> ("C:/main.lua", 1)
        didChangeFull "return 1 .. 1" ("C:/main.lua", 2)
        WhenMessages(List.length >> (<=) 3, Some <| TimeSpan.FromSeconds 5.)
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
let [<Fact>] hoverType() = async {
    let! r = serverActions id [
        "local x = 1 + 2" &> ("C:/main.lua", 1)
        Send <| Hover {
            textDocument = { uri = Uri "file:///C:/main.lua" }
            position = { line = 0; character = 6 }
        }
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
let [<Fact>] externalModuleErrorMessage() = async {
    let! r = serverActions id [
        "return 1 .. 2" &> ("C:/lib.lua", 1)
        "local x = require 'lib'" &> ("C:/main.lua", 1)
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
