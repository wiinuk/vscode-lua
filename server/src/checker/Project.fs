[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module LuaChecker.Project
open System.Collections.Immutable


let empty fileSystem initialGlobal caseSensitiveModuleResolve = {
    pathToSourceFile = HashMap.emptyWith <| DocumentPath.equalityComparer caseSensitiveModuleResolve
    projectRare = {
        fileSystem = fileSystem
        initialGlobal = initialGlobal
    }
}

let addSourceFileNoCheck path sourceFile project =
    { project with
        pathToSourceFile = HashMap.add path sourceFile project.pathToSourceFile
    }

let tryFind path project = HashMap.tryFind path project.pathToSourceFile
let remove path project = { project with pathToSourceFile = HashMap.remove path project.pathToSourceFile }
