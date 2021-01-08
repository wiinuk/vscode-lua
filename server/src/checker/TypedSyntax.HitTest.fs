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
type ITypedSyntaxVisitor =
    abstract Var: Var * TypeEnvironment -> unit
    abstract Reserved: ReservedVar * TypeEnvironment -> unit
    abstract Literal: S.Literal * Type * TypeEnvironment * LeafInfo voption -> unit

    abstract DocumentReserved: LeafSemantics D.Reserved -> unit
    abstract DocumentIdentifier: LeafSemantics D.Identifier -> unit
    abstract DocumentFieldSeparator: LeafSemantics D.FieldSeparator -> unit
    abstract DocumentFieldIdentifier: LeafSemantics D.FieldIdentifier -> unit
    abstract DocumentFieldVisibility: LeafSemantics D.FieldVisibility -> unit

module private rec IterateRange =
    open DocumentIterators
    type Name = S.Name

    [<Struct>]
    type HitEnv = {
        typeParameterOwners: Var list
        typeLevel: int
        range: Span
    }

    let intersectingWithSpan (env: _ inref) x = Span.isIntersecting env.range x
    let intersecting (env: _ inref) x = intersectingWithSpan &env x.trivia

    /// `( || )` の正格バージョン
    /// `x ||. y` = `let _x = x in let _y = y in _x || _y`
    let (||.) x y = x || y

    let envToTypeEnv (env: _ inref) = {
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

    let name (visitor: 'V byref when 'V :> ITypedSyntaxVisitor and 'V : struct) (env: _ inref) (Var(name = Name.Name x) as v) =
        intersectingWithSpan &env x.trivia.span && (
            visitor.Var(v, envToTypeEnv &env)
            true
        )

    let reserved (visitor: 'V byref when 'V :> ITypedSyntaxVisitor and 'V : struct) (env: _ inref) (ReservedVar(trivia = x) as v) =
        intersectingWithSpan &env x.span && (
            visitor.Reserved(v, envToTypeEnv &env)
            true
        )

    let literal (visitor: 'V byref when 'V :> ITypedSyntaxVisitor and 'V : struct) (env: _ inref) x t trivia =
        visitor.Literal(x, t, envToTypeEnv &env, trivia)
        true

    let nameList (v: _ byref) (env: _ inref) xs =
        let mutable result = false
        for x in (xs: _ list) do result <- result ||. name &v &env x
        result

    let nameList1 (v: _ byref) (env: _ inref) (NonEmptyList(x, xs)) =
        name &v &env x ||. nameList &v &env xs

    let varArg (v: 'V byref when 'V :> ITypedSyntaxVisitor and 'V : struct) (env: _ inref) x =
        v.Reserved(x, envToTypeEnv &env)
        true

    let expList (v: _ byref) (env: _ inref) xs =
        let mutable result = false
        for x in xs do result <- result ||. exp &v &env x
        result

    let expList1 (v: _ byref) (env: _ inref) (NonEmptyList(x, xs)) =
        exp &v &env x ||. expList &v &env xs

    let exp (v: _ byref) (env: _ inref) x =
        intersecting &env x &&

        match x.kind with
        | Literal(x, t, trivia) -> literal &v &env x t trivia
        | VarArg x -> varArg &v &env x
        | Function x -> funcBody &v &env x
        | NewTable x ->
            let mutable result = false
            for x in x do result <- result ||. field &v &env x
            result

        | Binary(x1, x2, x3) ->
            exp &v &env x1 ||.
            reserved &v &env x2 ||.
            exp &v &env x3

        | Unary(x1, x2) ->
            reserved &v &env x1 ||.
            exp &v &env x2

        | Wrap x -> exp &v &env x
        | TypeReinterpret(x1, x2) ->
            tags &v &env x1 ||.
            exp &v &env x2

        | Variable x -> name &v &env x

        | Index(x1, x2) ->
            exp &v &env x1 ||.
            exp &v &env x2

        | Member(x1, x2) ->
            exp &v &env x1 ||.
            name &v &env x2

        | Call(x1, x2) ->
            exp &v &env x1 ||.
            expList &v &env x2

        | CallWithSelf(x1, x2, x3) ->
            exp &v &env x1 ||.
            name &v &env x2 ||.
            expList &v &env x3

    let parameterList (v: _ byref) (env: _ inref) x =
        intersecting &env x &&
        match x.kind with
        | ParameterList(x1, x2) ->
            nameList &v &env x1 ||.
            (
                match x2 with
                | Some x2 -> reserved &v &env x2
                | _ -> false
            )

    let funcBody (v: _ byref) (env: _ inref) x =
        intersecting &env x &&
        let { kind = FuncBody(x1, x2) } = x
        (
            match x1 with
            | Some x -> parameterList &v &env x
            | _ -> false
        ) ||.
        block &v &env x2

    let field (v: _ byref) (env: _ inref) x =
        intersecting &env x &&
        match x.kind with
        | Init x -> exp &v &env x
        | MemberInit(x1, x2) ->
            name &v &env x1 ||.
            exp &v &env x2

        | IndexInit(x1, x2) ->
            exp &v &env x1 ||.
            exp &v &env x2

    let elseIfClause (v: _ byref) (env: _ inref) (ElseIf(x1, x2)) =
        exp &v &env x1 ||.
        block &v &env x2

    let elseClause (v: _ byref) (env: _ inref) x = block &v &env x

    let assignStat (v: _ byref) (env: _ inref) (x1, x2) =
        expList1 &v &env x1 ||.
        expList1 &v &env x2

    let whileStat (v: _ byref) (env: _ inref) (x1, x2) =
        exp &v &env x1 ||. block &v &env x2

    let repeatUntilStat (v: _ byref) (env: _ inref) (x1, x2) =
        block &v &env x1 ||.
        exp &v &env x2

    let ifStat (v: _ byref) (env: _ inref) (x1, x2, x3, x4) =
        exp &v &env x1 ||.
        block &v &env x2 ||.
        (
            let mutable result = false
            for x in x3 do result <- result ||. elseIfClause &v &env x
            result
        ) ||.
        match x4 with
        | Some x -> elseClause &v &env x
        | _ -> false

    let forStat (v: _ byref) (env: _ inref) (x1, x2, x3, x4, x5) =
        name &v &env x1 ||.
        exp &v &env x2 ||.
        exp &v &env x3 ||.
        (
            match x4 with
            | Some x -> exp &v &env x
            | _ -> false
        ) ||.
        block &v &env x5

    let forInStat (v: _ byref) (env: _ inref) (x1, x2, x3) =
        nameList1 &v &env x1 ||.
        expList1 &v &env x2 ||.
        block &v &env x3

    let functionDeclStat (v: _ byref) (env: _ inref) (x1, x2, x3, x4) =
        name &v &env x1 ||.
        nameList &v &env x2 ||.
        (
            match x3 with
            | Some x -> name &v &env x
            | _ -> false
        ) ||.
        funcBody &v &env x4

    let localFunctionStat (v: _ byref) (env: _ inref) (x1, x2, x3) =
        tags &v &env x1 ||.
        name &v &env x2 ||. (
            intersecting &env x3 &&
            let env = extendByTypeParameterOwner env x2
            funcBody &v &env x3
        )

    let localStat (v: _ byref) (env: _ inref) (x1, x2, x3) =
        tags &v &env x1 ||.
        nameList1 &v &env x2 ||.
        expList &v &env x3

    let stat (v: _ byref) (env: _ inref) x =
        let struct(span, (leadingTags, trailingTags)) = x.trivia
        tags &v &env leadingTags ||.
        (
            intersectingWithSpan &env span &&

            match x.kind with
            | FunctionCall x -> exp &v &env x
            | Assign(x1, x2) -> assignStat &v &env (x1, x2)
            | Do x -> block &v &env x
            | While(x1, x2) -> whileStat &v &env (x1, x2)
            | RepeatUntil(x1, x2) -> repeatUntilStat &v &env (x1, x2)
            | If(x1, x2, x3, x4) -> ifStat &v &env (x1, x2, x3, x4)
            | For(x1, x2, x3, x4, x5) -> forStat &v &env (x1, x2, x3, x4, x5)
            | ForIn(x1, x2, x3) -> forInStat &v &env (x1, x2, x3)
            | FunctionDecl(x1, x2, x3, x4) -> functionDeclStat &v &env (x1, x2, x3, x4)
            | LocalFunction(x1, x2, x3) -> localFunctionStat &v &env (x1, x2, x3)
            | Local(x1, x2, x3) -> localStat &v &env (x1, x2, x3)
        ) ||.
        tags &v &env trailingTags

    let lastStat (v: _ byref) (env: _ inref) x =
        let struct(span, (leadingTags, trailingTags)) = x.trivia
        tags &v &env leadingTags ||.
        (
            intersectingWithSpan &env span &&

            match x.kind with
            | Break -> false
            | Return x -> expList &v &env x
        ) ||.
        tags &v &env trailingTags

    let block (v: _ byref) (env: _ inref) x =
        let struct(span, (leadingTags, trailingTags)) = x.trivia
        tags &v &env leadingTags ||.
        (
            intersectingWithSpan &env span && (
                (
                    let mutable result = false
                    for x in x.kind.stats do result <- result ||. stat &v &env x
                    result
                ) ||.
                match x.kind.lastStat with
                | Some x -> lastStat &v &env x
                | _ -> false
            )
        ) ||.
        tags &v &env trailingTags

    let chunk (v: _ byref) (env: _ inref) x = block &v &env x

    module DocumentIterators =
        open IterateRange

        let reserved (visitor: 'V byref when 'V :> ITypedSyntaxVisitor and 'V : struct) (env: _ inref) (D.Annotated(k, _) as x) =
            intersecting &env k && (
                visitor.DocumentReserved x
                true
            )
        let identifier (visitor: 'V byref when 'V :> ITypedSyntaxVisitor and 'V : struct) (env: _ inref) (D.Annotated(Syntax.Name k, _) as x) =
            intersectingWithSpan &env k.trivia.span && (
                visitor.DocumentIdentifier x
                true
            )
        let fieldVisibility (visitor: 'V byref when 'V :> ITypedSyntaxVisitor and 'V : struct) (env: _ inref) (D.Annotated(k, _) as x) =
            intersecting &env k && (
                visitor.DocumentFieldVisibility x
                true
            )
        let fieldIdentifier (visitor: 'V byref when 'V :> ITypedSyntaxVisitor and 'V : struct) (env: _ inref) (D.Annotated(k, _) as x) =
            intersecting &env k && (
                visitor.DocumentFieldIdentifier x
                true
            )
        let fieldSeparator (visitor: 'V byref when 'V :> ITypedSyntaxVisitor and 'V : struct) (env: _ inref) (D.Annotated(k, _) as x) =
            intersecting &env k && (
                visitor.DocumentFieldSeparator x
                true
            )

        let tags (v: _ byref) (env: _ inref) x =
            intersecting &env x && (
                let mutable result = false
                for x in x.kind do result <- result ||. tag &v &env x
                result
            )

        let tag (v: _ byref) (env: _ inref) x =
            intersecting &env x &&
            let (D.Tag(x1, x2)) = x.kind
            reserved &v &env x1 ||.
            tagTail &v &env x2

        let tagTail (v: _ byref) (env: _ inref) x =
            intersecting &env x &&
            match x.kind with
            | D.GlobalTag(x1, x2, x3) -> globalTag &v &env (x1, x2, x3)
            | D.ClassTag(x1, x2, x3) -> classTag &v &env (x1, x2, x3)
            | D.TypeTag(x1, x2) -> typeTag &v &env (x1, x2)
            | D.FeatureTag(x1, x2) -> featureTag &v &env (x1, x2)
            | D.FieldTag(x1, x2, x3, x4) -> fieldTag &v &env (x1, x2, x3, x4)
            | D.GenericTag(x1, x2) -> genericTag &v &env (x1, x2)
            | D.UnknownTag(x1, x2) -> unknownTag &v &env (x1, x2)

        let globalTag (v: _ byref) (env: _ inref) (x1, x2, x3) =
            reserved &v &env x1 ||.
            identifier &v &env x2 ||.
            typeSign &v &env x3

        let classTag (v: _ byref) (env: _ inref) (x1, x2, x3) =
            reserved &v &env x1 ||.
            identifier &v &env x2 ||.
            match x3 with
            | Some(x1, x2) -> reserved &v &env x1 ||. typeSign &v &env x2
            | _ -> false

        let typeTag (v: _ byref) (env: _ inref) (x1, x2) =
            reserved &v &env x1 ||.
            typeSign &v &env x2

        let featureTag (v: _ byref) (env: _ inref) (x1, x2) =
            reserved &v &env x1 ||.
            identifier &v &env x2

        let fieldTag (v: _ byref) (env: _ inref) (x1, x2, x3, x4) =
            reserved &v &env x1 ||.
            (
                match x2 with
                | Some x -> fieldVisibility &v &env x
                | _ -> false
            ) ||.
            fieldIdentifier &v &env x3 ||.
            typeSign &v &env x4

        let genericTag (v: _ byref) (env: _ inref) (x1, x2) =
            reserved &v &env x1 ||.

            let (SepBy(x, xs)) = x2
            let mutable result = typeParameter &v &env x
            for sep, x in xs do result <- result ||. reserved &v &env sep ||. typeParameter &v &env x
            result

        let unknownTag (v: _ byref) (env: _ inref) (x1, _) =
            identifier &v &env x1
            // TODO:

        let typeParameter (v: _ byref) (env: _ inref) x =
            intersecting &env x &&

            match x.kind with
            | D.TypeParameter(x1, x2) ->
                identifier &v &env x1 ||.
                match x2 with
                | Some(x1, x2) ->
                    reserved &v &env x1 ||.
                    typeConstraints &v &env x2

                | _ -> false

            | D.VariadicTypeParameter(x1, x2, x3) ->
                identifier &v &env x1 ||.
                reserved &v &env x2 ||.
                match x3 with
                | Some x -> typeSign &v &env x
                | _ -> false

        let typeConstraints (v: _ byref) (env: _ inref) x = fields &v &env x
        let fields (v: _ byref) (env: _ inref) x =
            intersecting &env x &&

            let (D.Fields(x1, x2, x3, x4)) = x.kind
            reserved &v &env x1 ||.
            (
                let (SepBy(x, xs)) = x2
                let mutable result = field &v &env x
                for sep, x in xs do result <- result ||. fieldSeparator &v &env sep ||. field &v &env x
                result
            ) ||.
            (
                match x3 with
                | Some x -> fieldSeparator &v &env x
                | _ -> false
            ) ||.
            reserved &v &env x4

        let field (v: _ byref) (env: _ inref) x =
            intersecting &env x &&

            let (D.Field(x1, x2, x3)) = x.kind
            fieldIdentifier &v &env x1 ||.
            reserved &v &env x2 ||.
            typeSign &v &env x3

        let typeSign (v: _ byref) (env: _ inref) x =
            intersecting &env x &&

            match x.kind with
            | D.EmptyType(x1, x2) -> emptyType &v &env (x1, x2)
            | D.SingleMultiType(x1, x2, x3, x4) -> singleMultiType &v &env (x1, x2, x3, x4)
            | D.ArrayType(x1, x2, x3) -> arrayType &v &env (x1, x2, x3)
            | D.NilType x1 -> reserved &v &env x1
            | D.NamedType(x1, x2) -> namedType &v &env (x1, x2)
            | D.VariadicType x1 -> variadicType &v &env x1
            | D.ConstrainedType(x1, x2, x3) -> constrainedType &v &env (x1, x2, x3)
            | D.FunctionType(x1, x2, x3, x4, x5, x6) -> functionType &v &env (x1, x2, x3, x4, x5, x6) 
            | D.InterfaceType x1 -> fields &v &env x1
            | D.MultiType2(x1, x2, x3) -> multiType2 &v &env (x1, x2, x3)
            | D.WrappedType(x1, x2, x3) -> wrappedType &v &env (x1, x2, x3)

        let emptyType (v: _ byref) (env: _ inref) (x1, x2) =
            reserved &v &env x1 ||.
            reserved &v &env x2

        let singleMultiType (v: _ byref) (env: _ inref) (x1, x2, x3, x4) =
            reserved &v &env x1 ||.
            parameter &v &env x2 ||.
            reserved &v &env x3 ||.
            reserved &v &env x4

        let arrayType (v: _ byref) (env: _ inref) (x1, x2, x3) =
            typeSign &v &env x1 ||.
            reserved &v &env x2 ||.
            reserved &v &env x3

        let namedType (v: _ byref) (env: _ inref) (x1, x2) =
            identifier &v &env x1 ||.
            match x2 with
            | Some x -> genericArguments &v &env x
            | _ -> false

        let variadicType (v: _ byref) (env: _ inref) x =
            intersecting &env x &&

            let (D.VariadicTypeSign(x1, x2, x3)) = x.kind
            (
                match x1 with
                | Some x -> identifier &v &env x
                | _ -> false
            ) ||.
            reserved &v &env x2 ||.
            (
                match x3 with
                | Some x -> typeSign &v &env x
                | _ -> false
            )

        let constrainedType (v: _ byref) (env: _ inref) (x1, x2, x3) =
            typeSign &v &env x1 ||.
            reserved &v &env x2 ||.
            typeConstraints &v &env x3

        let functionType (v: _ byref) (env: _ inref) (x1, x2, x3, x4, x5, x6) =
            reserved &v &env x1 ||.
            reserved &v &env x2 ||.
            (
                match x3 with
                | Some x -> parameters &v &env x
                | _ -> false
            ) ||.
            reserved &v &env x4 ||.
            reserved &v &env x5 ||.
            typeSign &v &env x6

        let wrappedType (v: _ byref) (env: _ inref) (x1, x2, x3) =
            reserved &v &env x1 ||.
            typeSign &v &env x2 ||.
            reserved &v &env x3

        let multiType2 (v: _ byref) (env: _ inref) (x1, x2, x3) =
            parameter &v &env x1 ||.
            reserved &v &env x2 ||.
            parameters &v &env x3

        let genericArguments (v: _ byref) (env: _ inref) (D.GenericArguments(x1, x2, x3, x4)) =
            reserved &v &env x1 ||.
            (
                let (SepBy(x, xs)) = x2
                let mutable result = typeSign &v &env x
                for sep, x in xs do result <- result ||. reserved &v &env sep ||. typeSign &v &env x
                result
            ) ||.
            (
                match x3 with
                | Some x -> reserved &v &env x
                | _ -> false
            ) ||.
            reserved &v &env x4

        let parameter (v: _ byref) (env: _ inref) x =
            intersecting &env x &&

            let (D.Parameter(x1, x2)) = x.kind
            (
                match x1 with
                | Some(x1, x2) -> identifier &v &env x1 ||. reserved &v &env x2
                | _ -> false
            ) ||.
            typeSign &v &env x2

        let parameters (v: _ byref) (env: _ inref) (D.Parameters x1) =
            let (SepBy(x, xs)) = x1
            let mutable result = parameter &v &env x
            for sep, x in xs do result <- result ||. reserved &v &env sep ||. parameter &v &env x
            result

module Block =
    open IterateRange

    let iterateRange (visitor: _ byref) range source =
        let env = {
            range = range
            typeParameterOwners = []
            typeLevel = 0
        }
        chunk &visitor &env source

    let hitTest (visitor: _ byref) position source =
        iterateRange &visitor { start = position; end' = position + 1 } source
