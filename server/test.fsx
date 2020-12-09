open System
open System.IO

let localPath = "file.ext"
printfn $"localPath: {localPath}"
let currentDir = Environment.CurrentDirectory
printfn $"currentDir: {currentDir}"
let absolutePath  = Path.Combine(currentDir, localPath)
printfn $"absolutePath: {absolutePath}"
let absoluteUri = Uri absolutePath
printfn $"absoluteUri: {absoluteUri}"
let absoluteUriToPath = Uri("file:///" + absoluteUri.LocalPath).LocalPath
printfn $"absoluteUriToPath: {absoluteUriToPath}"
