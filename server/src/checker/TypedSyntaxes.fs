module rec LuaChecker.TypedSyntaxes
open LuaChecker
open LuaChecker.Primitives
open LuaChecker.TypeSystem
module S = LuaChecker.Syntaxes
module D = LuaChecker.Syntax.Documents


type Entity<'T,'S> = {
    span: Span
    entity: 'T
    state: 'S
}
type Entity<'T> = Entity<'T, HEmpty>
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
type Var = Var of name: S.Name * Type * LeafInfo voption
type ReservedVar = ReservedVar of trivia: S.Trivia * Syntax.TokenKind * Type * LeafInfo voption

type ParameterList = ParameterList' Entity
type ParameterList' = ParameterList of Var list * varArg: ReservedVar option

type Exp = Exp' Entity
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
    | TypeReinterpret of typeSign: D.TypeSign * Exp * toType: Type

    // FunctionCall
    | Call of Exp * Exp list
    | CallWithSelf of Exp * Var * Exp list

type Field = Field' Entity
type Field' =
    | Init of Exp
    | MemberInit of Var * Exp
    | IndexInit of Exp * Exp

type FuncBody = FuncBody' Entity
type FuncBody' = FuncBody of ParameterList option * Block

type LastStat = LastStat' Entity
type LastStat' =
    | Break
    | Return of Exp list

type ElseIf = | ElseIf of condition: Exp * ifTrue: Block

type Stat = Stat' Entity
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
    | LocalFunction of Var * FuncBody
    | Local of VarList * value: Exp list

type Block = Block' Entity
type Block' = {
    stats: Stat list
    lastStat: LastStat option
}
type ChunkInfo = {
    functionType: Scheme
    ancestorModulePaths: DocumentPath Set
    additionalGlobalEnv: Env
}
type Chunk = Entity<Block, ChunkInfo>
