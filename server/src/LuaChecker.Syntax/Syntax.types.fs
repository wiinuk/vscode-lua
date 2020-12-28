namespace LuaChecker.Syntax
open LuaChecker


type Trivia<'D> = {
    leadingTriviaLength: int
    mutable leadingDocument: 'D option
    span: Span
    trailingTriviaLength: int
    mutable trailingDocument: 'D option
}

[<RequireQualifiedAccess>]
type TokenKind =
    | Unknown

    /// `,`
    | Comma
    /// `.`
    | Dot
    /// `...`
    | Dot3

    | Function
    | End
    | Return
    | Break
    | If
    | Then
    | ElseIf
    | Else
    | While
    | Do
    | Repeat
    | Until
    | For
    | In
    | Local

    /// `[`
    | LSBracket
    /// `]`
    | RSBracket
    /// `{`
    | LCBracket
    /// `}`
    | RCBracket
    /// `(`
    | LBracket
    /// `)`
    | RBracket
    /// `=`
    | Assign

    /// `:`
    | Colon
    /// `;`
    | Semicolon
    /// `+`
    | Add
    /// `-`
    | Sub
    /// `*`
    | Mul
    /// `/`
    | Div
    /// `^`
    | Pow
    /// `%`
    | Mod
    /// `..`
    | Con
    ///<summary>`&lt;`</summary>
    | Lt
    ///<summary>`&lt;=`</summary>
    | Le
    /// `>`
    | Gt
    /// `>=`
    | Ge
    /// `==`
    | Eq
    /// `~=`
    | Ne
    | And
    | Or

    | Not
    /// `#`
    | Len

    | Nil
    | True
    | False
    | Number of double
    | Name of string
    | String of string

    // documentation comment

    /// `@`
    | At

[<RequireQualifiedAccess>]
type ParseError =
    | RequireFieldSep
    | RequireToken of TokenKind
    | RequireBinaryOp
    | RequireUnaryOp
    | RequireLiteral
    | RequireName
    | RequireString
    | RequireVar
    | DisallowedLeadingNewLine
    | RequireAnyStat
    | RequireAnyField
    | RequireAnyFieldKey
    | RequireAnyTypeSign
    | RequireNameOrDot3
    | RequireAssignStatOrFunctionCall
    | RequireEndOfSource
    | RequireNameOrLBracket
