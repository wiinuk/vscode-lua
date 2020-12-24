namespace LuaChecker
open LuaChecker.Primitives

[<RequireQualifiedAccess; Struct>]
type IdentifierScope =
    /// global declaration or definition, e.g. `---@global Global …`
    | Global
    /// local definition, e.g. `local Local …` `local function Local(…) …`
    | Local
    /// e.g. `x.Member`
    | Member

[<RequireQualifiedAccess; Struct>]
type IdentifierKind =
    /// e.g. `Variable` `Variable = …` `function Variable(…) …`
    | Variable
    /// parameter definition, e.g. `function(Parameter, …) …`
    | Parameter
    /// field name, e.g. `x.Field` `{ Field = … }`
    | Field
    /// method name, e.g. `x:Method(…)` `function x:Method(…) …`
    | Method

[<RequireQualifiedAccess; Struct>]
type DeclarationFeatures =
    | NoFeatures
    | GlobalRequire
    | GlobalPackage

[<RequireQualifiedAccess; Struct>]
type IdentifierRepresentation =
    /// e.g. `---@global Declaration …`
    | Declaration
    /// e.g. `local Definition …` `---@class Definition …`
    | Definition
    /// e.g. `Reference` `Reference = …` `x:Reference(…)` `function x:Reference(…) …` `function Reference(…) …` `---@type Reference`
    | Reference

type Declaration = {
    scheme: Scheme
    declarationFeatures: DeclarationFeatures
    declarationScope: IdentifierScope
    /// Variable or Parameter
    declarationKind: IdentifierKind
    /// Declaration or Definition
    declarationRepresentation: IdentifierRepresentation
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

type LeafSemanticsRare = {
    type': Type voption
    typeDefinition: TypeDefinition voption
    declaration: Declaration voption
}
module LeafSemanticsRare =
    let empty = {
        type' = ValueNone
        typeDefinition = ValueNone
        declaration = ValueNone
    }

[<System.Flags>]
type LeafFlags =
    | Empty             = 0b0000_0000uy
    | Keyword           = 0b0000_0001uy
    | Operator          = 0b0000_0010uy
    | TypeParameter     = 0b0000_0011uy
    | Parameter         = 0b0000_0100uy
    | Type              = 0b0000_0101uy
    | Field             = 0b0000_0110uy
    | Variable          = 0b0000_0111uy

    | Definition        = 0b0001_0000uy
    | Declaration       = 0b0010_0000uy
    | Global            = 0b0100_0000uy
    | Modification      = 0b1000_0000uy
    
    | _TypeMask         = 0b0000_1111uy
    | _ModifiersMask    = 0b1111_0000uy

[<Struct>]
type LeafSemantics = {
    leafFlags: LeafFlags
    leafRare: LeafSemanticsRare
}
module LeafSemantics =
    let empty = {
        leafFlags = LeafFlags.Empty
        leafRare = LeafSemanticsRare.empty
    }
