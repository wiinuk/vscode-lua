module LuaChecker.Server.Server
open LuaChecker
open LuaChecker.Server.Log
open LuaChecker.Server.ServerResources
open System
open System.Collections.Immutable
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
            let path = path |> Path.GetFullPath |> DocumentPath.ofPath
            ifDebug { trace $"adding {path} to project as global module." }
            path
        ]
        |> Checker.addInitialGlobalModules project

    ServerResources.resources <- ServerResources.loadFile options.resourcePaths []
    use writeAgent = WriteAgent.create {
        writer = output
    }
    let backgroundAgents =
        let count = max 1 Environment.ProcessorCount
        let agent = {
            writeAgent = writeAgent
            semanticTokensDataBuffer = ResizeArray()
            watch = Stopwatch()
        }
        ImmutableArray.CreateRange [
            for _ in 1..count -> BackgroundAgent.create agent
        ]

    use projectAgent = ProjectAgent.create {
        resourcePaths = options.resourcePaths
        writeAgent = writeAgent
        backgroundAgents = backgroundAgents

        pendingCheckPaths = Set.empty
        project = project
        root = rootUri
        documents = Map.empty
        responseHandlers = Map.empty
        nextRequestId = 1
        random = Random()
        watch = Stopwatch()
        nextDiagnosticsVersion = 1
    }
    let errorHandler e = raise e
    writeAgent.Error.Add errorHandler
    for agent in backgroundAgents do agent.Error.Add errorHandler
    projectAgent.Error.Add errorHandler

    try
        ifInfo { trace "%s" resources.LogMessages.ServerStarting }
        writeAgent.Start()
        for agent in backgroundAgents do agent.Start()
        projectAgent.Start()
        ReadAgent.start {
            projectAgent = projectAgent
            reader = input
        }
        ifInfo { trace "%s" resources.LogMessages.ServerTerminatedNormally }
    finally
        for agent in backgroundAgents do (agent :> IDisposable).Dispose()
