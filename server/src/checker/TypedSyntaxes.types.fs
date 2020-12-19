namespace LuaChecker
open LuaChecker.Primitives

[<RequireQualifiedAccess>]
type DefinitionScope =
    /// global declaration or definition, e.g. `---@global Global …`
    | Global
    /// local definition, e.g. `local Local …` `local function Local(…) …`
    | Local
    /// e.g. `x.Member`
    | Member

[<RequireQualifiedAccess>]
type IdentifierKind =
    /// e.g. `---@class Type`
    | Type
    /// e.g. `Variable` `Variable = …` `function Variable(…) …`
    | Variable
    /// parameter definition, e.g. `function(Parameter, …) …`
    | Parameter
    /// field name, e.g. `x.Field` `{ Field = … }`
    | Field
    /// method name, e.g. `x:Method(…)` `function x:Method(…) …`
    | Method

[<RequireQualifiedAccess>]
type DeclarationFeatures =
    | NoFeatures
    | GlobalRequire
    | GlobalPackage

type Declaration = {
    scheme: Scheme
    declarationFeatures: DeclarationFeatures
    declarationScope: DefinitionScope
    /// Variable or Parameter
    declarationKind: IdentifierKind
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
    stringMetaTableIndexType: Type list
}
module Env =
    let empty = {
        names = Map.empty
        types = Map.empty
        stringMetaTableIndexType = []
    }
    let merge mergeNames mergeTypes child parent =
        let types =
            parent.types
            |> Map.fold (fun types parentName parentDefs ->
                let mergedDefs =
                    match Map.tryFind parentName types with
                    | ValueSome ds -> mergeTypes ds parentDefs
                    | _ -> parentDefs
                Map.add parentName mergedDefs types
            ) child.types

        let names =
            parent.names
            |> Map.fold (fun names parentName parentDefs ->
                let mergedDefs =
                    match Map.tryFind parentName names with
                    | ValueSome defs -> mergeNames defs parentDefs
                    | _ -> parentDefs
                Map.add parentName mergedDefs names
            ) child.names

        let stringMetaTableIndexType = child.stringMetaTableIndexType @ parent.stringMetaTableIndexType
        { types = types; names = names; stringMetaTableIndexType = stringMetaTableIndexType }
