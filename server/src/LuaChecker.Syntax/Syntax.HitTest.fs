namespace LuaChecker.Syntax
open LuaChecker
open LuaChecker.Syntaxes

type SyntaxVisitor<'This,'Result> = {
    name: struct ('This * Name) -> 'Result
    reserved: struct ('This * Trivia * TokenKind) -> 'Result
    literal: struct ('This * Literal) -> 'Result
}

module private rec HitTesters =
    type HitEnv<'This,'Result> = {
        visitor: SyntaxVisitor<'This,'Result>
        visitorThis: 'This
        index: int
    }

    let inside env x = Span.inRange env.index x.trivia
    let outside env x = not <| inside env x
    let inToken env x = Span.inRange env.index x.trivia.span

    let inline option f = function
        | None -> ValueNone
        | Some x -> f x

    let inline (?>) option ifNone =
        match option with
        | ValueSome _ as r -> r
        | _ -> ifNone()

    let inline tuple2 (f1, f2) (x1, x2) =
        match f1 x1 with
        | ValueSome _ as r -> r
        | _ -> f2 x2

    let inline list f xs =
        let mutable list = xs
        let mutable result = ValueNone
        while
            match list with
            | [] -> false
            | x::xs ->
                match f x with
                | ValueSome _ as r ->
                    result <- r
                    false
                | _ ->
                    list <- xs
                    true
            do ()
        result

    let inline sepBy findSep find (SepBy(x, sepXs)) =
        find x ?> fun _ ->
        list (fun (sep, x) -> findSep sep ?> fun _ -> find x) sepXs

    let hitReserved env kind x = env.visitor.reserved(env.visitorThis, x.trivia, kind) |> ValueSome
    let reserved env kind x = if inToken env x then hitReserved env kind x else ValueNone
    let comma env x = reserved env TokenKind.Comma x

    let inline separateByComma env find xs =
        if outside env xs then ValueNone else
        sepBy (comma env) (find env) xs.kind

    let nameList env xs = separateByComma env name xs
    let name env (Name x as n) =
        if inToken env x
        then env.visitor.name(env.visitorThis, n) |> ValueSome
        else ValueNone

    let expList env xs = separateByComma env exp xs
    let exp env x =
        if outside env x then ValueNone else

        match x.kind with
        | Literal x -> env.visitor.literal(env.visitorThis, x) |> ValueSome
        | VarArg x -> hitReserved env TokenKind.Dot3 x
        | Function(x1, x2) ->
            reserved env TokenKind.Function x1 ?> fun _ ->
            funcBody env x2

        | PrefixExp x -> prefixExp env x
        | NewTable x -> tableConstructor env x
        | Binary(x1, x2, x3) ->
            exp env x1 ?> fun _ ->
            reserved env (TokenKind.ofBinaryOpKind x2.kind) x2 ?> fun _ ->
            exp env x3

        | Unary(x1, x2) ->
            reserved env (TokenKind.ofUnaryOpKind x1.kind) x1 ?> fun _ ->
            exp env x2

    let prefixExp env x =
        if outside env x then ValueNone else
        match x.kind with
        | Apply x -> functionCall env x
        | Var x -> var env x
        | Wrap(x1, x2, x3) ->
            reserved env TokenKind.LBracket x1 ?> fun _ ->
            exp env x2 ?> fun _ ->
            reserved env TokenKind.RBracket x3

    let var env x =
        if outside env x then ValueNone else
        match x.kind with
        | Variable x -> name env x
        | Index(x1, x2, x3, x4) ->
            prefixExp env x1 ?> fun _ ->
            reserved env TokenKind.LSBracket x2 ?> fun _ ->
            exp env x3 ?> fun _ ->
            reserved env TokenKind.RSBracket x4

        | Member(x1, x2, x3) ->
            prefixExp env x1 ?> fun _ ->
            reserved env TokenKind.Dot x2 ?> fun _ ->
            name env x3

    let args env x =
        if outside env x then ValueNone else
        match x.kind with
        | StringArg(StringLiteral x) ->

            // TODO:
            let x = { kind = String x.kind; trivia = x.trivia }
            env.visitor.literal(env.visitorThis, x) |> ValueSome

        | Args(x1, x2, x3) ->
            reserved env TokenKind.LBracket x1 ?> fun _ ->
            option (expList env) x2 ?> fun _ ->
            reserved env TokenKind.RBracket x3

        | TableArg x -> tableConstructor env x

    let functionCall env x =
        if outside env x then ValueNone else
        match x.kind with
        | Call(x1, x2) ->
            prefixExp env x1 ?> fun _ ->
            args env x2

        | CallWithSelf(x1, x2, x3, x4) ->
            prefixExp env x1 ?> fun _ ->
            reserved env TokenKind.Colon x2 ?> fun _ ->
            name env x3 ?> fun _ ->
            args env x4

    let funcName env x =
        if outside env x then ValueNone else
        let { kind = FuncName(x1, x2, x3) } = x
        name env x1 ?> fun _ ->
        list (tuple2(reserved env TokenKind.Dot, name env)) x2 ?> fun _ ->
        option (tuple2(reserved env TokenKind.Colon, name env)) x3

    let parameterList env x =
        if outside env x then ValueNone else
        match x.kind with
        | VarParameter x -> reserved env TokenKind.Dot3 x
        | ParameterList(x1, x2) ->
            nameList env x1 ?> fun _ ->
            option (tuple2 (comma env, reserved env TokenKind.Dot3)) x2

    let funcBody env x =
        if outside env x then ValueNone else
        let { kind = FuncBody(x1, x2, x3, x4, x5) } = x
        reserved env TokenKind.LBracket x1 ?> fun _ ->
        option (parameterList env) x2 ?> fun _ ->
        reserved env TokenKind.RBracket x3 ?> fun _ ->
        block env x4 ?> fun _ ->
        reserved env TokenKind.End x5

    let field env x =
        if outside env x then ValueNone else
        match x.kind with
        | Init x -> exp env x
        | MemberInit(x1, x2, x3) ->
            name env x1 ?> fun _ ->
            reserved env TokenKind.Eq x2 ?> fun _ ->
            exp env x3

        | IndexInit(x1, x2, x3, x4, x5) ->
            reserved env TokenKind.LSBracket x1 ?> fun _ ->
            exp env x2 ?> fun _ ->
            reserved env TokenKind.RSBracket x3 ?> fun _ ->
            reserved env TokenKind.Eq x4 ?> fun _ ->
            exp env x5

    let fieldSep env x = reserved env (TokenKind.ofFieldSepKind x.kind) x

    let fieldList env (FieldList(x1, x2)) =
        sepBy (fieldSep env) (field env) x1 ?> fun _ ->
        option (fieldSep env) x2

    let tableConstructor env x =
        if outside env x then ValueNone else

        let (TableConstructor(x1, x2, x3)) = x.kind
        reserved env TokenKind.LCBracket x1 ?> fun _ ->
        option (fieldList env) x2 ?> fun _ ->
        reserved env TokenKind.RCBracket x3

    let elseIfClause env x =
        if outside env x then ValueNone else

        let { kind = ElseIf(x1, x2, x3, x4) } = x
        reserved env TokenKind.ElseIf x1 ?> fun _ ->
        exp env x2 ?> fun _ ->
        reserved env TokenKind.Then x3 ?> fun _ ->
        block env x4

    let elseClause env x =
        if outside env x then ValueNone else

        let { kind = Else(x1, x2) } = x
        reserved env TokenKind.Else x1 ?> fun _ ->
        block env x2

    let assignStat env (x1, x2, x3) =
        separateByComma env var x1 ?> fun _ ->
        reserved env TokenKind.Assign x2 ?> fun _ ->
        expList env x3

    let doStat env (x1, x2, x3) =
        reserved env TokenKind.Do x1 ?> fun _ ->
        block env x2 ?> fun _ ->
        reserved env TokenKind.End x3

    let whileStat env (x1, x2, x3, x4, x5) =
        reserved env TokenKind.While x1 ?> fun _ ->
        exp env x2 ?> fun _ ->
        reserved env TokenKind.Do x3 ?> fun _ ->
        block env x4 ?> fun _ ->
        reserved env TokenKind.End x5

    let repeatUntilStat env (x1, x2, x3, x4) =
        reserved env TokenKind.Repeat x1 ?> fun _ ->
        block env x2 ?> fun _ ->
        reserved env TokenKind.Until x3 ?> fun _ ->
        exp env x4

    let ifStat env (x1, x2, x3, x4, x5, x6, x7) =
        reserved env TokenKind.If x1 ?> fun _ ->
        exp env x2 ?> fun _ ->
        reserved env TokenKind.Then x3 ?> fun _ ->
        block env x4 ?> fun _ ->
        list (elseIfClause env) x5 ?> fun _ ->
        option (elseClause env) x6 ?> fun _ ->
        reserved env TokenKind.End x7

    let forStat env (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) =
        reserved env TokenKind.For x1 ?> fun _ ->
        name env x2 ?> fun _ ->
        reserved env TokenKind.Eq x3 ?> fun _ ->
        exp env x4 ?> fun _ ->
        comma env x5 ?> fun _ ->
        exp env x6 ?> fun _ ->
        option (tuple2(comma env, exp env)) x7 ?> fun _ ->
        reserved env TokenKind.Do x8 ?> fun _ ->
        block env x9 ?> fun _ ->
        reserved env TokenKind.End x10

    let forInStat env (x1, x2, x3, x4, x5, x6, x7) =
        reserved env TokenKind.For x1 ?> fun _ ->
        nameList env x2 ?> fun _ ->
        reserved env TokenKind.In x3 ?> fun _ ->
        expList env x4 ?> fun _ ->
        reserved env TokenKind.Do x5 ?> fun _ ->
        block env x6 ?> fun _ ->
        reserved env TokenKind.End x7

    let functionDeclStat env (x1, x2, x3) =
        reserved env TokenKind.Function x1 ?> fun _ ->
        funcName env x2 ?> fun _ ->
        funcBody env x3

    let localFunctionStat env (x1, x2, x3, x4) =
        reserved env TokenKind.Local x1 ?> fun _ ->
        reserved env TokenKind.Function x2 ?> fun _ ->
        name env x3 ?> fun _ ->
        funcBody env x4

    let localStat env (x1, x2, x3) =
        reserved env TokenKind.Local x1 ?> fun _ ->
        nameList env x2 ?> fun _ ->
        option (tuple2 (reserved env TokenKind.Assign, expList env)) x3

    let stat env x =
        if outside env x then ValueNone else

        match x.kind with
        | FunctionCall x -> functionCall env x
        | Assign(x1, x2, x3) -> assignStat env (x1, x2, x3)
        | Do(x1, x2, x3) -> doStat env (x1, x2, x3)
        | While(x1, x2, x3, x4, x5) -> whileStat env (x1, x2, x3, x4, x5)
        | RepeatUntil(x1, x2, x3, x4) -> repeatUntilStat env (x1, x2, x3, x4)
        | If(x1, x2, x3, x4, x5, x6, x7) -> ifStat env (x1, x2, x3, x4, x5, x6, x7)
        | For(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) -> forStat env (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10)
        | ForIn(x1, x2, x3, x4, x5, x6, x7) -> forInStat env (x1, x2, x3, x4, x5, x6, x7)
        | FunctionDecl(x1, x2, x3) -> functionDeclStat env (x1, x2, x3)
        | LocalFunction(x1, x2, x3, x4) -> localFunctionStat env (x1, x2, x3, x4)
        | Local(x1, x2, x3) -> localStat env (x1, x2, x3)

    let lastStat env x =
        if outside env x then ValueNone else

        match x.kind with
        | Break x -> reserved env TokenKind.Break x
        | Return(x1, x2) -> tuple2 (reserved env TokenKind.Return, option (expList env)) (x1, x2)

    let block env x =
        if not <| inToken env x then ValueNone else

        x.kind.stats
        |> list (tuple2 (stat env, option (reserved env TokenKind.Semicolon)))
        ?> fun _ -> option (tuple2 (lastStat env, option (reserved env TokenKind.Semicolon))) x.kind.lastStat

    let chunk env x = block env x

module internal HitTest =
    open HitTesters


    let block visitor visitorThis position source =
        let env = { visitor = visitor; visitorThis = visitorThis; index = position }
        chunk env source
