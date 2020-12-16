module rec LuaChecker.Syntaxes
open LuaChecker.Primitives
open LuaChecker.Syntax


type Trivia = Trivia<Documents.ParseResult>
type Token<'T> = Token<'T, Trivia>
type Token = Token<HEmpty, Trivia>
type Name = Documents.ParseResult Name
type SeparateBy<'S,'T> = Source<SepBy<'S,'T>>

[<Struct>]
type StringLiteral = StringLiteral of Token<string>

type LiteralKind =
    | Nil
    | True
    | False
    | Number of double
    | String of string
type Literal = Token<LiteralKind>

type FieldSepKind =
    | Comma
    | Semicolon

type FieldSep = Token<FieldSepKind>

type BinaryOpKind =
    | Or
    | And
    | Lt | Gt | Le | Ge | Eq | Ne
    // right assoc
    | Con
    | Add | Sub
    | Mul | Div | Mod
    // right assoc
    | Pow

type BinaryOp = Token<BinaryOpKind>

type UnaryOpKind =
    | Neg
    | Not
    | Len

type UnaryOp = Token<UnaryOpKind>

type NameList = SeparateBy<Token (* `,` *), Name>
type FuncName = Source<FuncName'>
type FuncName' = | FuncName of Name * path: (Token (* `.` *) * Name) list * methodName: (Token (* `:` *) * Name) option

type ParameterList = Source<ParameterList'>
type ParameterList' =
    /// `...`
    | VarParameter of dot3: Token
    | ParameterList of NameList * commaAndDot3: (Token (* `,` *) * Token (* `...` *)) option

type PrefixExp = Source<PrefixExp'>

type Exp' =
    | Literal of Literal
    /// `...´
    | VarArg of dot3: Token
    | Function of function': Token * FuncBody
    | PrefixExp of PrefixExp
    | NewTable of TableConstructor
    | Binary of Exp * BinaryOp * Exp
    | Unary of UnaryOp * Exp

type Exp = Source<Exp'>
type Var = Source<Var'>

type ExpList = SeparateBy<Token (* `,` *), Exp>

type PrefixExp' =
    | Var of Var
    | Apply of FunctionCall
    /// `( exp )`
    | Wrap of lBracket: Token * Exp * rBracket: Token

type Var' =
    | Variable of Name
    /// `prefixExp [ exp ]`
    | Index of PrefixExp * lsBracket: Token * Exp * rsBracket: Token
    | Member of PrefixExp * dot: Token * Name

type FunctionCall' =
    | Call of PrefixExp * Args
    | CallWithSelf of PrefixExp * colon: Token * Name * Args

type FunctionCall = Source<FunctionCall'>

type Field' =
    | Init of Exp
    | MemberInit of Name * eq: Token * Exp
    | IndexInit of lsBracket: Token * Exp * rsBracket: Token * eq: Token * Exp

type Field = Source<Field'>

type FieldList = FieldList of SepBy<FieldSep, Field> * FieldSep option

type TableConstructor = Source<TableConstructor'>
/// `{ fieldList? }`
type TableConstructor' = TableConstructor of lcBracket: Token * FieldList option * rcBracket: Token

type Args = Source<Args'>
type Args' =
    | StringArg of string: StringLiteral
    | Args of lBracket: Token * args: ExpList option * rBracket: Token
    | TableArg of TableConstructor

type VarList = SeparateBy<Token (* `,` *), Var>

type FuncBody = Source<FuncBody'>
type FuncBody' = FuncBody of lBracket: Token * ParameterList option * rBracket: Token * Block * end': Token

type LastStat' =
    | Break of break': Token
    | Return of return': Token * ExpList option
type LastStat = Source<LastStat'>

type ElseIf = Source<ElseIf'>
type ElseIf' = | ElseIf of elseif: Token * condition: Exp * then': Token * ifTrue: Block
type Else = Source<Else'>
type Else' = | Else of else': Token * ifFalse: Block

type Stat' =
    | FunctionCall of FunctionCall
    | Assign of VarList * eq: Token * ExpList
    | Do of do': Token * Block * end': Token
    | While of while': Token * Exp * do': Token * Block * end': Token
    | RepeatUntil of repeat: Token * Block * until: Token * Exp
    | If of if': Token * condition: Exp * then': Token * ifTrue: Block * elseIfs: ElseIf list * else': Else option * end': Token
    | For of for': Token * Name * eq: Token * start: Exp * comma: Token * stop: Exp * commaAndStep: (Token * Exp) option * do': Token * Block * end': Token
    | ForIn of for': Token * NameList * in': Token * ExpList * do': Token * Block * end': Token
    | FunctionDecl of function': Token * FuncName * FuncBody
    | LocalFunction of local: Token * function': Token * Name * FuncBody
    | Local of local: Token * NameList * value: (Token (* `=` *) * ExpList) option

type Stat = Source<Stat'>

[<Struct>]
type Block' = {
    stats: (Stat * Token (* `;` *) option) list
    lastStat: (LastStat * Token (* `;` *) option) option
}
type Block = Token<Block'>
