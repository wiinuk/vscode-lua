[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module LuaChecker.Syntax.TokenKind
open LuaChecker
open LuaChecker.Syntaxes
type private K = Syntax.TokenKind


let ofBinaryOpKind = function
    | Add -> K.Add
    | Sub -> K.Sub
    | Mul -> K.Mul
    | Div -> K.Div
    | Pow -> K.Pow
    | Mod -> K.Mod
    | Con -> K.Con
    | Lt -> K.Lt
    | Le -> K.Le
    | Gt -> K.Gt
    | Ge -> K.Ge
    | Eq -> K.Eq
    | Ne -> K.Ne
    | And -> K.And
    | Or -> K.Or

let ofLiteralKind = function
    | Nil -> K.Nil
    | True -> K.True
    | False -> K.False
    | Number x -> K.Number x
    | String x -> K.String x

let ofUnaryOpKind = function
    | Neg -> K.Sub
    | Not -> K.Not
    | Len -> K.Len

let ofFieldSepKind = function
    | Comma -> K.Comma
    | Semicolon -> K.Semicolon
