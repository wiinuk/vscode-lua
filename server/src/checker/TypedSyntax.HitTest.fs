namespace LuaChecker
open LuaChecker
open LuaChecker.TypedSyntaxes
open LuaChecker.Primitives
module S = Syntaxes
module D = Syntax.Documents


[<Struct>]
type TypeEnvironment = {
    typeParameterOwners: Var list
    typeLevel: int
}
type TypedSyntaxVisitor<'This> = {
    var: struct ('This * Var * TypeEnvironment) -> unit
    reserved: struct ('This * ReservedVar * TypeEnvironment) -> unit
    literal: struct ('This * S.Literal * Type * TypeEnvironment * LeafInfo voption) -> unit
    typeTag: struct ('This * D.TypeSign * Type * TypeEnvironment) -> unit
}

module private rec Testers =
    type Name = S.Name

    type HitEnvNoUpdate<'This> = {
        visitor: TypedSyntaxVisitor<'This>
        visitorThis: 'This
        index: int
    }
    [<Struct>]
    type HitEnv<'This> = {
        typeParameterOwners: Var list
        typeLevel: int
        noUpdate: HitEnvNoUpdate<'This>
    }

    let inside env x = Span.inRange env.index x.span

    let inline option f = function
        | None -> false
        | Some x -> f x

    let inline list f xs =
        let mutable list = xs
        let mutable result = false
        while
            match list with
            | [] -> false
            | x::xs ->
                if f x then
                    result <- true
                    false
                else
                    list <- xs
                    true
            do ()
        result

    let inline nonEmptyList find (NonEmptyList(x, xs)) =
        find x ||
        list find xs

    let nameList env xs = nonEmptyList (name env) xs

    let envToTypeEnv env = {
        typeParameterOwners = env.typeParameterOwners
        typeLevel = env.typeLevel
    }
    let name env (Var(name = Name.Name x) as v) =
        if not <| Span.inRange env.noUpdate.index x.trivia.span then false else
        env.noUpdate.visitor.var(env.noUpdate.visitorThis, v, envToTypeEnv env)
        true

    let reserved env (ReservedVar(trivia = x) as v) =
        if not <| Span.inRange env.noUpdate.index x.span then false else
        env.noUpdate.visitor.reserved(env.noUpdate.visitorThis, v, envToTypeEnv env)
        true

    let literal env x t trivia =
        env.noUpdate.visitor.literal(env.noUpdate.visitorThis, x, t, envToTypeEnv env, trivia)
        true

    let varArg env x =
        env.noUpdate.visitor.reserved(env.noUpdate.visitorThis, x, envToTypeEnv env)
        true

    let expList env xs = nonEmptyList (exp env) xs
    let exp env x =
        inside env.noUpdate x &&

        match x.entity with
        | Literal(x, t, trivia) -> literal env x t trivia
        | VarArg x -> varArg env x
        | Function x -> funcBody env x
        | NewTable x -> list (field env) x
        | Binary(x1, x2, x3) ->
            exp env x1 ||
            reserved env x2 ||
            exp env x3

        | Unary(x1, x2) ->
            reserved env x1 ||
            exp env x2

        | Wrap x -> exp env x
        | TypeReinterpret(x1, x2, t) ->
            if Span.inRange env.noUpdate.index x1.trivia then
                env.noUpdate.visitor.typeTag(env.noUpdate.visitorThis, x1, t, envToTypeEnv env)
                true
            else
                exp env x2

        | Variable x -> name env x

        | Index(x1, x2) ->
            exp env x1 ||
            exp env x2

        | Member(x1, x2) ->
            exp env x1 ||
            name env x2

        | Call(x1, x2) ->
            exp env x1 ||
            list (exp env) x2

        | CallWithSelf(x1, x2, x3) ->
            exp env x1 ||
            name env x2 ||
            list (exp env) x3

    let parameterList env x =
        inside env.noUpdate x &&
        match x.entity with
        | ParameterList(x1, x2) ->
            list (name env) x1 ||
            option (reserved env) x2

    let funcBody env x =
        inside env.noUpdate x &&
        let { entity = FuncBody(x1, x2) } = x
        option (parameterList env) x1 ||
        block env x2

    let field env x =
        inside env.noUpdate x &&
        match x.entity with
        | Init x -> exp env x
        | MemberInit(x1, x2) ->
            name env x1 ||
            exp env x2

        | IndexInit(x1, x2) ->
            exp env x1 ||
            exp env x2

    let elseIfClause env (ElseIf(x1, x2)) =
        exp env x1 ||
        block env x2

    let elseClause env x = block env x

    let assignStat env (x1, x2) =
        nonEmptyList (exp env) x1 ||
        expList env x2

    let whileStat env (x1, x2) =
        exp env x1 || block env x2

    let repeatUntilStat env (x1, x2) =
        block env x1 ||
        exp env x2

    let ifStat env (x1, x2, x3, x4) =
        exp env x1 ||
        block env x2 ||
        list (elseIfClause env) x3 ||
        option (elseClause env) x4

    let forStat env (x1, x2, x3, x4, x5) =
        name env x1 ||
        exp env x2 ||
        exp env x3 ||
        option (exp env) x4 ||
        block env x5

    let forInStat env (x1, x2, x3) =
        nameList env x1 ||
        expList env x2 ||
        block env x3

    let functionDeclStat env (x1, x2, x3, x4) =
        name env x1 ||
        list (name env) x2 ||
        option (name env) x3 ||
        funcBody env x4

    let localFunctionStat env (x1, x2) =
        name env x1 ||

        let (Var(_, t, _)) = x1
        let vars =
            match t with
            | { kind = TypeAbstraction(vs, _) } -> vs
            | _ -> []

        let env =
            match vars with
            | [] -> { env with typeLevel = env.typeLevel + 1 }
            | _ -> { env with typeLevel = env.typeLevel + 1; typeParameterOwners = x1::env.typeParameterOwners }

        funcBody env x2

    let localStat env (x1, x2) =
        nameList env x1 || list (exp env) x2

    let stat env x =
        inside env.noUpdate x &&

        match x.entity with
        | FunctionCall x -> exp env x
        | Assign(x1, x2) -> assignStat env (x1, x2)
        | Do x -> block env x
        | While(x1, x2) -> whileStat env (x1, x2)
        | RepeatUntil(x1, x2) -> repeatUntilStat env (x1, x2)
        | If(x1, x2, x3, x4) -> ifStat env (x1, x2, x3, x4)
        | For(x1, x2, x3, x4, x5) -> forStat env (x1, x2, x3, x4, x5)
        | ForIn(x1, x2, x3) -> forInStat env (x1, x2, x3)
        | FunctionDecl(x1, x2, x3, x4) -> functionDeclStat env (x1, x2, x3, x4)
        | LocalFunction(x1, x2) -> localFunctionStat env (x1, x2)
        | Local(x1, x2) -> localStat env (x1, x2)

    let lastStat env x =
        inside env.noUpdate x &&

        match x.entity with
        | Break -> false
        | Return x -> list (exp env) x

    let block env x =
        inside env.noUpdate x && (
            list (stat env) x.entity.stats ||
            option (lastStat env) x.entity.lastStat
        )

    let chunk env x = block env x

module Block =
    open Testers

    let hitTest visitor visitorThis position source =
        let env = {
            noUpdate = {
                visitor = visitor
                visitorThis = visitorThis
                index = position
            }
            typeParameterOwners = []
            typeLevel = 0
        }
        chunk env source
