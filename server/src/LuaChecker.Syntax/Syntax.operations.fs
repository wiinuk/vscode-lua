namespace LuaChecker.Syntax
open LuaChecker
open LuaChecker.Syntaxes
open LuaChecker.Syntax
open System.Text.RegularExpressions


module LiteralKind =
    open type System.Double
    let equalsER v1 v2 =
        match v1, v2 with
        | Number v1, Number v2 -> v1 = v2 || (IsNaN v1 && IsNaN v2)
        | _ -> v1 = v2

module Token =
    let measure x = x.trivia.span
    let inline map mapping x = { kind = x.kind; trivia = mapping x.trivia }
    let inline sourced { kind = kind; trivia = trivia } mapping = { kind = mapping kind; trivia = trivia }
    let make trivia kind = { kind = kind; trivia = trivia }

module Source =
    let measure x = x.trivia

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Name =
    let measure (Name x) = Token.measure x

    let private reservedNames = Set [
        "and"; "break"; "do"; "else"; "elseif"; "end";
        "false"; "for"; "function"; "if"; "in"; "local";
        "nil"; "not"; "or"; "repeat"; "return"; "then";
        "true"; "until"; "while";
    ]
    let isValid n =
        Regex.IsMatch(n, @"^[\p{L}_][\p{L}0-9_]*\z") &&
        not (Set.contains n reservedNames)

module TableConstructor =
    let measure (TableConstructor(lcBracket = x1; rcBracket = x2)) = Span.merge (Token.measure x1) (Token.measure x2)

module Args =
    let measure = function
        | Args(x1, _, x2) -> Span.merge (Token.measure x1) (Token.measure x2)
        | TableArg x -> Source.measure x
        | StringArg(StringLiteral x) -> Token.measure x

module ParameterList =
    let measure = function
        | ParameterList(x1, x2) ->
            let s1 = Source.measure x1
            match x2 with
            | None -> s1
            | Some(_, x2) -> Span.merge s1 (Token.measure x2)

        | VarParameter x -> Token.measure x

module FuncName =
    let measure (FuncName(x1, x2, x3)) =
        let s1 = Name.measure x1
        let s2 = Span.list (Span.tuple2 (Token.measure, Name.measure)) x2
        let s3 = Span.option (Span.tuple2 (Token.measure, Name.measure)) x3
        Span.merge s1 (Span.merge s2 s3)

module FuncBody =
    let measure (FuncBody(lBracket = x1; end' = x2)) = Span.merge (Token.measure x1) (Token.measure x2)

module Field =
    let measure = function
        | IndexInit(lsBracket = x1; rsBracket = x2) -> Span.merge (Token.measure x1) (Token.measure x2)
        | Init x -> Source.measure x
        | MemberInit(x1, _, x2) -> Span.merge (Name.measure x1) (Source.measure x2)

module FunctionCall =
    let measure = function
        | Call(x1, x2) -> Span.merge (Source.measure x1) (Source.measure x2)
        | CallWithSelf(x1, _, _, x2) -> Span.merge (Source.measure x1) (Source.measure x2)

module PrefixExp =
    let measure = function
        | Apply x -> Source.measure x
        | Var x -> Source.measure x
        | Wrap(x1, _, x2) -> Span.merge (Token.measure x1) (Token.measure x2)

module Exp =
    let measure = function
        | Literal x -> Token.measure x
        | VarArg x -> Token.measure x
        | NewTable x -> Source.measure x
        | Function(x1, x2) -> Span.merge (Token.measure x1) (Source.measure x2)
        | PrefixExp x -> Source.measure x
        | Binary(x1, _, x2) -> Span.merge (Source.measure x1) (Source.measure x2)
        | Unary(x1, x2) -> Span.merge (Token.measure x1) (Source.measure x2)

module Var =
    let measure = function
        | Index(x1, _, _, x2) -> Span.merge (Source.measure x1) (Token.measure x2)
        | Member(x1, _, x2) -> Span.merge (Source.measure x1) (Name.measure x2)
        | Variable x -> Name.measure x

module ElseIf =
    let measure (ElseIf(elseif = x1; ifTrue = x2)) = Span.merge (Token.measure x1) (Token.measure x2)

module Else =
    let measure (Else(x1, x2)) = Span.merge (Token.measure x1) (Token.measure x2)

module Stat =
    let measure = function
        | Assign(x1, _, x2) -> Span.merge (Source.measure x1) (Source.measure x2)
        | FunctionCall x -> Source.measure x
        | Do(x1, _, x2)
        | While(while' = x1; end' = x2)
        | If(if' = x1; end' = x2)
        | For(for' = x1; end' = x2)
        | ForIn(for' = x1; end' = x2) -> Span.merge (Token.measure x1) (Token.measure x2)
        | RepeatUntil(x1, _, _, x2) -> Span.merge (Token.measure x1) (Source.measure x2)
        | FunctionDecl(x1, _, x2)
        | LocalFunction(x1, _, _, x2) -> Span.merge (Token.measure x1) (Source.measure x2)
        | Local(x1, x2, x2') ->
            let x2 =
                match x2' with
                | None -> Source.measure x2
                | Some(_, x2) -> Source.measure x2

            Span.merge (Token.measure x1) x2

module LastStat =
    let measure = function
        | Break x -> Token.measure x
        | Return(x1, x2) ->

        match x2 with
        | None -> Token.measure x1
        | Some x2 -> Span.merge (Token.measure x1) (Source.measure x2)

module Block =
    let measure x =
        let x1 = Span.list (Span.tuple2 (Source.measure, Span.option Token.measure)) x.stats
        let x2 = Span.option (Span.tuple2 (Source.measure, Span.option Token.measure)) x.lastStat
        Span.merge x1 x2
