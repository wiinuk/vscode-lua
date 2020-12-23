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

    documentReserved: struct ('This * LeafSemantics D.Reserved) -> unit
    documentIdentifier: struct ('This * LeafSemantics D.Identifier) -> unit
    documentFieldSeparator: struct ('This * LeafSemantics D.FieldSeparator) -> unit
    documentFieldIdentifier: struct ('This * LeafSemantics D.FieldIdentifier) -> unit
    documentFieldVisibility: struct ('This * LeafSemantics D.FieldVisibility) -> unit
}
module TypedSyntaxVisitor =
    let withDefaultOperation defaultOperation = {
        var = fun struct(this, _, _) -> defaultOperation this
        reserved = fun struct(this, _, _) -> defaultOperation this
        literal = fun struct(this, _, _, _, _) -> defaultOperation this

        documentReserved = fun struct (this, _) -> defaultOperation this
        documentIdentifier = fun struct (this, _ ) -> defaultOperation this
        documentFieldSeparator = fun struct (this, _) -> defaultOperation this
        documentFieldIdentifier = fun struct (this, _) -> defaultOperation this
        documentFieldVisibility = fun struct (this, _) -> defaultOperation this
    }
    let noop = {
        var = ignore
        reserved = ignore
        literal = ignore

        documentReserved = ignore
        documentIdentifier = ignore
        documentFieldSeparator = ignore
        documentFieldIdentifier = ignore
        documentFieldVisibility = ignore
    }

module private rec IterateRange =
    open DocumentIterators
    type Name = S.Name

    type HitEnvNoUpdate<'This> = {
        visitor: TypedSyntaxVisitor<'This>
        visitorThis: 'This
        range: Span
    }
    [<Struct>]
    type HitEnv<'This> = {
        typeParameterOwners: Var list
        typeLevel: int
        noUpdate: HitEnvNoUpdate<'This>
    }

    let intersectingWithSpan env x = Span.isIntersecting env.noUpdate.range x
    let intersecting env x = intersectingWithSpan env x.trivia

    let inline option f = function
        | Some x -> f x
        | _ -> false

    /// `( || )` の正格バージョン
    /// `x ||. y` = `let _x = x in let _y = y in _x || _y`
    let (||.) x y = x || y

    let inline tuple2 f1 f2 (x1, x2) =
        f1 x1 ||. f2 x2

    let inline list f xs =
        let mutable result = false
        for x in (xs: _ list) do result <- result ||. f x
        result

    let inline nonEmptyList find (NonEmptyList(x, xs)) =
        find x ||.
        list find xs

    let inline sepBy findSep find (SepBy(x, xs)) =
        let mutable result = find x
        for sep, x in (xs: _ list) do result <- result ||. findSep sep ||. find x
        result

    let nameList env xs = nonEmptyList (name env) xs

    let envToTypeEnv env = {
        typeParameterOwners = env.typeParameterOwners
        typeLevel = env.typeLevel
    }
    let extendByTypeParameterOwner env (Var(varType = t) as x1) =
        let vars =
            match t with
            | { kind = TypeAbstraction(vs, _) } -> vs
            | _ -> []

        match vars with
        | [] -> { env with HitEnv.typeLevel = env.typeLevel + 1 }
        | _ -> { env with typeLevel = env.typeLevel + 1; typeParameterOwners = x1::env.typeParameterOwners }

    let name env (Var(name = Name.Name x) as v) =
        intersectingWithSpan env x.trivia.span && (
            env.noUpdate.visitor.var(env.noUpdate.visitorThis, v, envToTypeEnv env)
            true
        )

    let reserved env (ReservedVar(trivia = x) as v) =
        intersectingWithSpan env x.span && (
            env.noUpdate.visitor.reserved(env.noUpdate.visitorThis, v, envToTypeEnv env)
            true
        )

    let literal env x t trivia =
        env.noUpdate.visitor.literal(env.noUpdate.visitorThis, x, t, envToTypeEnv env, trivia)
        true

    let varArg env x =
        env.noUpdate.visitor.reserved(env.noUpdate.visitorThis, x, envToTypeEnv env)
        true

    let expList env xs = nonEmptyList (exp env) xs
    let exp env x =
        intersecting env x &&

        match x.kind with
        | Literal(x, t, trivia) -> literal env x t trivia
        | VarArg x -> varArg env x
        | Function x -> funcBody env x
        | NewTable x -> list (field env) x
        | Binary(x1, x2, x3) ->
            exp env x1 ||.
            reserved env x2 ||.
            exp env x3

        | Unary(x1, x2) ->
            reserved env x1 ||.
            exp env x2

        | Wrap x -> exp env x
        | TypeReinterpret(x1, x2) ->
            tags env x1 ||.
            exp env x2

        | Variable x -> name env x

        | Index(x1, x2) ->
            exp env x1 ||.
            exp env x2

        | Member(x1, x2) ->
            exp env x1 ||.
            name env x2

        | Call(x1, x2) ->
            exp env x1 ||.
            list (exp env) x2

        | CallWithSelf(x1, x2, x3) ->
            exp env x1 ||.
            name env x2 ||.
            list (exp env) x3

    let parameterList env x =
        intersecting env x &&
        match x.kind with
        | ParameterList(x1, x2) ->
            list (name env) x1 ||.
            option (reserved env) x2

    let funcBody env x =
        intersecting env x &&
        let { kind = FuncBody(x1, x2) } = x
        option (parameterList env) x1 ||.
        block env x2

    let field env x =
        intersecting env x &&
        match x.kind with
        | Init x -> exp env x
        | MemberInit(x1, x2) ->
            name env x1 ||.
            exp env x2

        | IndexInit(x1, x2) ->
            exp env x1 ||.
            exp env x2

    let elseIfClause env (ElseIf(x1, x2)) =
        exp env x1 ||.
        block env x2

    let elseClause env x = block env x

    let assignStat env (x1, x2) =
        nonEmptyList (exp env) x1 ||.
        expList env x2

    let whileStat env (x1, x2) =
        exp env x1 ||. block env x2

    let repeatUntilStat env (x1, x2) =
        block env x1 ||.
        exp env x2

    let ifStat env (x1, x2, x3, x4) =
        exp env x1 ||.
        block env x2 ||.
        list (elseIfClause env) x3 ||.
        option (elseClause env) x4

    let forStat env (x1, x2, x3, x4, x5) =
        name env x1 ||.
        exp env x2 ||.
        exp env x3 ||.
        option (exp env) x4 ||.
        block env x5

    let forInStat env (x1, x2, x3) =
        nameList env x1 ||.
        expList env x2 ||.
        block env x3

    let functionDeclStat env (x1, x2, x3, x4) =
        name env x1 ||.
        list (name env) x2 ||.
        option (name env) x3 ||.
        funcBody env x4

    let localFunctionStat env (x1, x2) =
        name env x1 ||. (
            intersecting env x2 &&
            funcBody (extendByTypeParameterOwner env x1) x2
        )

    let localStat env (x1, x2) =
        nameList env x1 ||. list (exp env) x2

    let stat env x =
        let struct(span, (leadingTags, trailingTags)) = x.trivia
        tags env leadingTags ||.
        (
            intersectingWithSpan env span &&

            match x.kind with
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
        ) ||.
        tags env trailingTags

    let lastStat env x =
        let struct(span, (leadingTags, trailingTags)) = x.trivia
        tags env leadingTags ||.
        (
            intersectingWithSpan env span &&

            match x.kind with
            | Break -> false
            | Return x -> list (exp env) x
        ) ||.
        tags env trailingTags

    let block env x =
        let struct(span, (leadingTags, trailingTags)) = x.trivia
        tags env leadingTags ||.
        (
            intersectingWithSpan env span && (
                list (stat env) x.kind.stats ||.
                option (lastStat env) x.kind.lastStat
            )
        ) ||.
        tags env trailingTags

    let chunk env x = block env x

    module DocumentIterators =
        open IterateRange

        let reserved env (D.Annotated(k, _) as x) =
            intersecting env k && (
                env.noUpdate.visitor.documentReserved(env.noUpdate.visitorThis, x)
                true
            )
        let identifier env (D.Annotated(Syntax.Name k, _) as x) =
            intersectingWithSpan env k.trivia.span && (
                env.noUpdate.visitor.documentIdentifier(env.noUpdate.visitorThis, x)
                true
            )
        let fieldVisibility env (D.Annotated(k, _) as x) =
            intersecting env k && (
                env.noUpdate.visitor.documentFieldVisibility(env.noUpdate.visitorThis, x)
                true
            )
        let fieldIdentifier env (D.Annotated(k, _) as x) =
            intersecting env k && (
                env.noUpdate.visitor.documentFieldIdentifier(env.noUpdate.visitorThis, x)
                true
            )
        let fieldSeparator env (D.Annotated(k, _) as x) =
            intersecting env k && (
                env.noUpdate.visitor.documentFieldSeparator(env.noUpdate.visitorThis, x)
                true
            )

        let tags env x =
            intersecting env x &&
            list (tag env) x.kind

        let tag env x =
            intersecting env x &&
            let (D.Tag(x1, x2)) = x.kind
            reserved env x1 ||.
            tagTail env x2

        let tagTail env x =
            intersecting env x &&
            match x.kind with
            | D.GlobalTag(x1, x2, x3) -> globalTag env (x1, x2, x3)
            | D.ClassTag(x1, x2, x3) -> classTag env (x1, x2, x3)
            | D.TypeTag(x1, x2) -> typeTag env (x1, x2)
            | D.FeatureTag(x1, x2) -> featureTag env (x1, x2)
            | D.FieldTag(x1, x2, x3, x4) -> fieldTag env (x1, x2, x3, x4)
            | D.GenericTag(x1, x2) -> genericTag env (x1, x2)
            | D.UnknownTag(x1, x2) -> unknownTag env (x1, x2)

        let globalTag env (x1, x2, x3) =
            reserved env x1 ||.
            identifier env x2 ||.
            typeSign env x3

        let classTag env (x1, x2, x3) =
            reserved env x1 ||.
            identifier env x2 ||.
            option (tuple2 (reserved env) (typeSign env)) x3

        let typeTag env (x1, x2) =
            reserved env x1 ||.
            typeSign env x2

        let featureTag env (x1, x2) =
            reserved env x1 ||.
            identifier env x2

        let fieldTag env (x1, x2, x3, x4) =
            reserved env x1 ||.
            option (fieldVisibility env) x2 ||.
            fieldIdentifier env x3 ||.
            typeSign env x4

        let genericTag env (x1, x2) =
            reserved env x1 ||.
            sepBy (reserved env) (typeParameter env) x2

        let unknownTag env (x1, _) =
            identifier env x1
            // TODO:

        let typeParameter env x =
            intersecting env x &&

            match x.kind with
            | D.TypeParameter(x1, x2) ->
                identifier env x1 ||.
                option (tuple2 (reserved env) (typeConstraints env)) x2

            | D.VariadicTypeParameter(x1, x2, x3) ->
                identifier env x1 ||.
                reserved env x2 ||.
                option (typeSign env) x3

        let typeConstraints env x = fields env x
        let fields env x =
            intersecting env x &&

            let (D.Fields(x1, x2, x3, x4)) = x.kind
            reserved env x1 ||.
            sepBy (fieldSeparator env) (field env) x2 ||.
            option (fieldSeparator env) x3 ||.
            reserved env x4

        let field env x =
            intersecting env x &&

            let (D.Field(x1, x2, x3)) = x.kind
            fieldIdentifier env x1 ||.
            reserved env x2 ||.
            typeSign env x3

        let typeSign env x =
            intersecting env x &&

            match x.kind with
            | D.EmptyType(x1, x2) -> emptyType env (x1, x2)
            | D.SingleMultiType(x1, x2, x3, x4) -> singleMultiType env (x1, x2, x3, x4)
            | D.ArrayType(x1, x2, x3) -> arrayType env (x1, x2, x3)
            | D.NamedType(x1, x2) -> namedType env (x1, x2)
            | D.VariadicType x1 -> variadicType env x1
            | D.ConstrainedType(x1, x2, x3) -> constrainedType env (x1, x2, x3)
            | D.FunctionType(x1, x2, x3, x4, x5, x6) -> functionType env (x1, x2, x3, x4, x5, x6) 
            | D.InterfaceType x1 -> fields env x1
            | D.MultiType2(x1, x2, x3) -> multiType2 env (x1, x2, x3)
            | D.WrappedType(x1, x2, x3) -> wrappedType env (x1, x2, x3)

        let emptyType env (x1, x2) =
            reserved env x1 ||.
            reserved env x2

        let singleMultiType env (x1, x2, x3, x4) =
            reserved env x1 ||.
            parameter env x2 ||.
            reserved env x3 ||.
            reserved env x4

        let arrayType env (x1, x2, x3) =
            typeSign env x1 ||.
            reserved env x2 ||.
            reserved env x3

        let namedType env (x1, x2) =
            identifier env x1 ||
            option (genericArguments env) x2

        let variadicType env x =
            intersecting env x &&

            let (D.VariadicTypeSign(x1, x2, x3)) = x.kind
            option (identifier env) x1 ||.
            reserved env x2 ||.
            option (typeSign env) x3

        let constrainedType env (x1, x2, x3) =
            typeSign env x1 ||.
            reserved env x2 ||.
            typeConstraints env x3

        let functionType env (x1, x2, x3, x4, x5, x6) =
            reserved env x1 ||.
            reserved env x2 ||.
            option (parameters env) x3 ||.
            reserved env x4 ||.
            reserved env x5 ||.
            typeSign env x6

        let wrappedType env (x1, x2, x3) =
            reserved env x1 ||.
            typeSign env x2 ||.
            reserved env x3

        let multiType2 env (x1, x2, x3) =
            parameter env x1 ||.
            reserved env x2 ||.
            parameters env x3

        let genericArguments env (D.GenericArguments(x1, x2, x3, x4)) =
            reserved env x1 ||.
            sepBy (reserved env) (typeSign env) x2 ||.
            option (reserved env) x3 ||.
            reserved env x4

        let parameter env x =
            intersecting env x &&

            let (D.Parameter(x1, x2)) = x.kind
            option (tuple2 (identifier env) (reserved env)) x1 ||.
            typeSign env x2

        let parameters env (D.Parameters x1) =
            sepBy (reserved env) (parameter env) x1

module Block =
    open IterateRange

    let iterateRange visitor visitorThis range source =
        let env = {
            noUpdate = {
                visitor = visitor
                visitorThis = visitorThis
                range = range
            }
            typeParameterOwners = []
            typeLevel = 0
        }
        chunk env source

    let hitTest visitor visitorThis position source =
        iterateRange visitor visitorThis { start = position; end' = position + 1 } source
