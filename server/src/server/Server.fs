module LuaChecker.Server.Server
open LuaChecker
open LuaChecker.Server.Log
open System
open System.Diagnostics
open System.IO


type ServerCreateOptions = {
    resourcePaths: string list
    backgroundCheckDelay: TimeSpan
    fileSystem: FileSystem
    luaPath: string option
    platform: PlatformID option
    luaExeDirectory: string option
    caseSensitiveModuleResolve: bool
    globalModulePaths: string list
}
module ServerCreateOptions =
    let defaultOptions = {
        resourcePaths = []
        backgroundCheckDelay = TimeSpan.FromMilliseconds 2000.
        fileSystem = FileSystem.systemIO
        luaPath = None
        platform = None
        luaExeDirectory = None
        caseSensitiveModuleResolve = true
        globalModulePaths = [
            "standard.d.lua"
        ]
    }

let start withOptions (input, output) =
    let options = withOptions ServerCreateOptions.defaultOptions
    let packagePath = TopEnv.packagePath options.luaPath (defaultArg options.platform Environment.OSVersion.Platform) options.luaExeDirectory
    let rootUri = Uri "file:///"

    let project = Project.empty options.fileSystem (Checker.standardEnv packagePath) options.caseSensitiveModuleResolve
    let project =
        [ for path in options.globalModulePaths ->
            Path.Combine(Environment.CurrentDirectory, path) |> Path.GetFullPath |> Uri |> DocumentPath.ofUri rootUri
        ]
        |> Checker.addInitialGlobalModules project

    let resources = ServerResources.loadFile options.resourcePaths
    let writeAgent = WriteAgent.create {
        writer = output
        resources = resources
    }
    let projectAgent = ProjectAgent.create {
        resources = resources
        pendingBackgroundCheckPaths = Set.empty
        project = project
        root = rootUri
        documents = Map.empty
        writer = writeAgent
        responseHandlers = Map.empty
        nextRequestId = 1
        watch = Stopwatch()
    }
    let errorHandler e = ifError { trace $"%A{e}" }
    writeAgent.Error.Add errorHandler
    projectAgent.Error.Add errorHandler

    ifInfo { trace "%s" resources.LogMessages.ServerStarting }
    writeAgent.Start()
    projectAgent.Start()
    ReadAgent.start {
        resources = resources
        writeAgent = writeAgent
        projectAgent = projectAgent
        reader = input
    }
    ifInfo { trace "%s" resources.LogMessages.ServerTerminatedNormally }
