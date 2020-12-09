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
let absoluteUriToLocalPath = absoluteUri.LocalPath
printfn $"absoluteUriToLocalPath: {absoluteUriToLocalPath}"
let absoluteUriToPath = Uri("file:///" + absoluteUriToLocalPath).LocalPath
printfn $"absoluteUriToPath: {absoluteUriToPath}"
