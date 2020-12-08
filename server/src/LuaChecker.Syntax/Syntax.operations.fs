namespace LuaChecker.Syntax
open LuaChecker
open LuaChecker.Syntaxes
open LuaChecker.Syntax
open System.Text.RegularExpressions


[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Trivia =
    let createEmpty() = {
        leadingTriviaLength = 0
        leadingDocument = None
        span = Span.empty
        trailingTriviaLength = 0
        trailingDocument = None
    }
    let merge t1 t2 = {
        leadingTriviaLength = t1.leadingTriviaLength
        leadingDocument = t1.leadingDocument
        span = Span.merge t1.span t2.span
        trailingTriviaLength = t2.trailingTriviaLength
        trailingDocument = t2.trailingDocument
    }

module Token =
    let measure x = x.trivia.span
    let map mapping x = { kind = x.kind; trivia = mapping x.trivia }

module Source =
    let measure x = x.trivia

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Name =
    let measure (Name x) = Token.measure x
    let map mapping (Name x) = Name <| Token.map mapping x

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

module private rec MapRec =
    let inline option f = function None -> None | Some x -> Some(f x)
    let inline tuple2 (f1, f2) (x1, x2) = f1 x1, f2 x2
    let inline trivial map (mapSpan: Span -> Span, (mapTrivia: Trivia -> Trivia)) x = { kind = map (mapSpan, mapTrivia) x.kind; trivia = mapSpan x.trivia }

    let token (_, f) x = Token.map f x
    let name (_, f) x = Name.map f x
    let nameList f x = trivial (fun f x -> SepBy.mapSep (token f) (name f) x) f x

    let exp f x = trivial exp' f x
    let exp' f = function
        | Literal x -> Literal <| token f x
        /// `...´
        | VarArg x -> VarArg <| token f x
        | Function(x1, x2) -> Function(token f x1, funcBody f x2)
        | PrefixExp x -> PrefixExp <| prefixExp f x
        | NewTable x -> NewTable <| tableConstructor f x
        | Binary(x1, x2, x3) -> Binary(exp f x1, token f x2, exp f x3)
        | Unary(x1, x2) -> Unary(token f x1, exp f x2)

    let expList f x = trivial (fun f x -> SepBy.mapSep (token f) (exp f) x) f x

    let var f x = trivial var' f x
    let var' f = function
        | Variable x -> Variable <| name f x
        | Index(x1, x2, x3, x4) -> Index(prefixExp f x1, token f x2, exp f x3, token f x4)
        | Member(x1, x2, x3) -> Member(prefixExp f x1, token f x2, name f x3)

    let args f x = trivial args' f x
    let args' f = function
        | Args(x1, x2, x3) -> Args(token f x1, option (expList f) x2, token f x3)
        | StringArg(StringLiteral x) -> StringArg <| StringLiteral(token f x)
        | TableArg x -> TableArg <| tableConstructor f x

    let functionCall f x = trivial functionCall' f x
    let functionCall' f = function
        | Call(x1, x2) -> Call(prefixExp f x1, args f x2)
        | CallWithSelf(x1, x2, x3, x4) -> CallWithSelf(prefixExp f x1, token f x2, name f x3, args f x4)

    let prefixExp f x = trivial prefixExp' f x
    let prefixExp' f = function
        | Apply x -> Apply <| functionCall f x
        | Var x -> Var <| var f x
        | Wrap(x1, x2, x3) -> Wrap(token f x1, exp f x2, token f x3)

    let varList f x = trivial (fun f x -> SepBy.mapSep (token f) (var f) x) f x

    let field f x = trivial field' f x
    let field' f = function
        | Init x -> Init <| exp f x
        | IndexInit(x1, x2, x3, x4, x5) -> IndexInit(token f x1, exp f x2, token f x3, token f x4, exp f x5)
        | MemberInit(x1, x2, x3) -> MemberInit(name f x1, token f x2, exp f x3)

    let fieldList f (FieldList(x1, x2)) = FieldList(SepBy.mapSep (token f) (field f) x1, option (token f) x2)
    let tableConstructor f x = trivial tableConstructor' f x
    let tableConstructor' f (TableConstructor(x1, x2, x3)) =
        TableConstructor(token f x1, option (fieldList f) x2, token f x3)

    let parameterList f x = trivial parameterList' f x
    let parameterList' f = function
        | ParameterList(x1, x2) -> ParameterList(nameList f x1, option (tuple2 (token f, token f)) x2)
        | VarParameter x -> VarParameter(token f x)

    let funcBody f x = trivial funcBody' f x
    let funcBody' f (FuncBody(x1, x2, x3, x4, x5)) =
        FuncBody(token f x1, option (parameterList f) x2, token f x3, block f x4, token f x5)

    let funcName f x = trivial funcName' f x
    let funcName' f (FuncName(x1, x2, x3)) =
        FuncName(name f x1, List.map (tuple2(token f, name f)) x2, option (tuple2(token f, name f)) x3)

    let elseIfClause f x = trivial elseIfClause' f x
    let elseIfClause' f (ElseIf(x1, x2, x3, x4)) = ElseIf(token f x1, exp f x2, token f x3, block f x4)
    let elseClause f x = trivial elseClause' f x
    let elseClause' f (Else(x1, x2)) = Else(token f x1, block f x2)

    let stat f x = trivial stat' f x
    let stat' f = function
        | Assign(x1, x2, x3) -> Assign(varList f x1, token f x2, expList f x3)
        | FunctionCall x -> FunctionCall <| functionCall f x
        | Do(x1, x2, x3) -> Do(token f x1, block f x2, token f x3)
        | While(x1, x2, x3, x4, x5) -> While(token f x1, exp f x2, token f x3, block f x4, token f x5)
        | RepeatUntil(x1, x2, x3, x4) -> RepeatUntil(token f x1, block f x2, token f x3, exp f x4)
        | If(x1, x2, x3, x4, x5, x6, x7) ->
            If(
                token f x1, exp f x2, token f x3, block f x4,
                List.map (elseIfClause f) x5, option (elseClause f) x6, token f x7
            )
        | For(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) ->
            For(
                token f x1, name f x2, token f x3, exp f x4, token f x5, exp f x6,
                option (tuple2(token f, exp f)) x7,
                token f x8, block f x9, token f x10
            )
        | ForIn(x1, x2, x3, x4, x5, x6, x7) ->
            ForIn(token f x1, nameList f x2, token f x3, expList f x4, token f x5, block f x6, token f x7)

        | FunctionDecl(x1, x2, x3) -> FunctionDecl(token f x1, funcName f x2, funcBody f x3)
        | LocalFunction(x1, x2, x3, x4) -> LocalFunction(token f x1, token f x2, name f x3, funcBody f x4)
        | Local(x1, x2, x3) -> Local(token f x1, nameList f x2, option (tuple2(token f, expList f)) x3)

    let lastStat f x = trivial lastStat' f x
    let lastStat' f = function
        | Break x -> Break <| token f x
        | Return(x1, x2) -> Return(token f x1, option (expList f) x2)

    let block ((_, mapTrivia) as f) x = {
        kind = block' f x.kind
        trivia = mapTrivia x.trivia
    }

    let block' f x = {
        stats = List.map (tuple2(stat f, option (token f))) x.stats
        lastStat = option (tuple2(lastStat f, option (token f))) x.lastStat
    }

module FuncName =
    let measure (FuncName(x1, x2, x3)) =
        let s1 = Name.measure x1
        let s2 = Span.list (Span.tuple2 (Token.measure, Name.measure)) x2
        let s3 = Span.option (Span.tuple2 (Token.measure, Name.measure)) x3
        Span.merge s1 (Span.merge s2 s3)

module FuncBody =
    let measure (FuncBody(lBracket = x1; end' = x2)) = Span.merge (Token.measure x1) (Token.measure x2)
    let map mapping x = MapRec.funcBody mapping x

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

    let map mapping x = MapRec.exp mapping x

module Var =
    let measure = function
        | Index(x1, _, _, x2) -> Span.merge (Source.measure x1) (Token.measure x2)
        | Member(x1, _, x2) -> Span.merge (Source.measure x1) (Name.measure x2)
        | Variable x -> Name.measure x

    let map mapping x = MapRec.var mapping x

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

    let map mapping x = MapRec.stat mapping x

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

    let map mapping x = MapRec.block mapping x
    let hitTest visitor visitorThis position x = HitTest.block visitor visitorThis position x
