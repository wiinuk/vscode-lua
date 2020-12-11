module LuaChecker.Server.Program
open LuaChecker
open LuaChecker.Server.Protocol
open LuaChecker.Server.Log
open System


[<EntryPoint>]
let main _ =
    let input = MessageReader.borrowStream <| Console.OpenStandardInput()
    use output = MessageWriter.borrowStream <| Console.OpenStandardOutput()
    try
        Server.start id (input, output)
        0
    with e ->
        ifError { trace "%A" e }
        1
