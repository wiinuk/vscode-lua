open System
open System.IO

let localPath = "file.ext"
printfn "localPath: %s" localPath
let currentDir = Environment.CurrentDirectory
printfn "currentDir: %s" currentDir
let absolutePath  = Path.Combine(currentDir, localPath)
printfn "absolutePath: %s" absolutePath
let absoluteUri = Uri absolutePath
printfn "absoluteUri: %A" absoluteUri
let absoluteUriToLocalPath = absoluteUri.LocalPath
printfn "absoluteUriToLocalPath: %s" absoluteUriToLocalPath
let absoluteUriToPath = Uri("file://" + absoluteUriToLocalPath).LocalPath
printfn "absoluteUriToPath: %s" absoluteUriToPath
