module rec LuaChecker.TypedSyntaxes
open LuaChecker
open LuaChecker.Primitives
open LuaChecker.TypeSystem
module S = LuaChecker.Syntaxes
module D = LuaChecker.Syntax.Documents


type Token<'T> = Token<'T, Span>
type Tags = LeafSemantics D.Tag list Token
type NeighbourTags = Tags * Tags

type LeafInfo = {
    externalModulePath: DocumentPath voption
    schemeInstantiation: (Scheme * struct(TypeParameterId * Type) list) voption
}
module LeafInfo =
    let empty = {
        externalModulePath = ValueNone
        schemeInstantiation = ValueNone
    }

type VarList = Var NonEmptyList

type Var =
    | Var of
        scope: IdentifierScope *
        kind: IdentifierKind *
        representation: IdentifierRepresentation *
        name: S.Name *
        varType: Type *
        leaf: LeafInfo voption

type ReservedVar = ReservedVar of trivia: S.Trivia * kind: Syntax.TokenKind * Type * LeafInfo voption

type ParameterList = ParameterList' Token
type ParameterList' = ParameterList of Var list * varArg: ReservedVar option

type Exp = Exp' Token
type Exp' =
    | Literal of S.Literal * Type * LeafInfo voption
    | VarArg of ReservedVar
    | Function of FuncBody
    | NewTable of Field list
    | Binary of Exp * ReservedVar * Exp
    | Unary of ReservedVar * Exp

    // Var
    | Variable of Var
    | Index of Exp * Exp
    | Member of Exp * Var

    // PrefixExp
    /// `( exp )`
    | Wrap of Exp
    /// `--[[ typeSign ]]( exp )`
    | TypeReinterpret of tags: Tags * Exp

    // FunctionCall
    | Call of Exp * Exp list
    | CallWithSelf of Exp * Var * Exp list

type Field = Field' Token
type Field' =
    | Init of Exp
    | MemberInit of Var * Exp
    | IndexInit of Exp * Exp

type FuncBody = FuncBody' LuaChecker.Syntax.Source
type FuncBody' = FuncBody of ParameterList option * Block

type LastStat = Token<LastStat', struct(Span * NeighbourTags)>
type LastStat' =
    | Break
    | Return of Exp list

type ElseIf = | ElseIf of condition: Exp * ifTrue: Block

type Stat = Token<Stat', struct(Span * NeighbourTags)>
type Stat' =
    | FunctionCall of Exp
    | Assign of Exp NonEmptyList * Exp NonEmptyList
    | Do of Block
    | While of Exp * Block
    | RepeatUntil of Block * Exp
    | If of condition: Exp * ifTrue: Block * elseIfs: ElseIf list * else': Block option
    | For of Var * start: Exp * stop: Exp * step: Exp option * Block
    | ForIn of VarList * Exp NonEmptyList * Block
    | FunctionDecl of Var * path: Var list * self: Var option * FuncBody
    | LocalFunction of modifierTags: Tags * Var * FuncBody
    | Local of modifierTags: Tags * VarList * value: Exp list

type Block = Token<Block', struct(Span * NeighbourTags)>
type Block' = {
    stats: Stat list
    lastStat: LastStat option
}
type Chunk = {
    semanticTree: Block
    typeSubstitute: Type Subst
    functionType: Scheme
    ancestorModulePaths: DocumentPath Set
    additionalGlobalEnv: Env
}
