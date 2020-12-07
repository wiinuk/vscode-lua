namespace LuaChecker
open LuaChecker.Primitives


[<RequireQualifiedAccess>]
type DeclarationKind =
    | NoFeatures
    | GlobalRequire
    | GlobalPackage

type Declaration = {
    scheme: Scheme
    declarationKind: DeclarationKind
    location: Location option
}
[<RequireQualifiedAccess>]
type SystemTypeCode =
    | Nil
    | Boolean
    | Number
    | String
    ///<summary>table&lt;K, V&gt;</summary>
    | Table
    ///<summary>thread&lt;TInput..., TOutput...&gt;</summary>
    | Thread

[<RequireQualifiedAccess>]
type TypeDefinitionKind =
    | System of SystemTypeCode
    | Alias of Type
    | Variable of name: string * Type

type TypeDefinition = {
    typeKind: TypeDefinitionKind
    locations: Location list
}
[<Struct>]
type Env = {
    names: Map<string, Declaration NonEmptyList>
    types: Map<string, TypeDefinition NonEmptyList>
}
module Env =
    let empty = {
        names = Map.empty
        types = Map.empty
    }
