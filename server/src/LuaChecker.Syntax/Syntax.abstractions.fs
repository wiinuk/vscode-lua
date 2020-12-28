namespace rec LuaChecker.Syntax
open LuaChecker
open LuaChecker.Primitives
open LuaChecker.Syntax
open LuaChecker.Syntaxes
open LuaChecker.Syntax.SyntaxShapes
open LuaChecker.Syntax.SyntaxVisitor
type private K = Syntax.TokenKind


type ISyntaxShape<'Syntax> =
    inherit IShape
    abstract EnumerateChildren: visitorShape: The<'VisitorShape> * visitor: 'Visitor byref * syntax: 'Syntax * result: 'Result outref -> bool
        when 'VisitorShape :> ISyntaxVisitorShape<'Visitor,'Result>
        and 'VisitorShape : struct

    abstract EnumerateChildrenReverse: visitorShape: The<'VisitorShape> * visitor: 'Visitor byref * syntax: 'Syntax * result: 'Result outref -> bool
        when 'VisitorShape :> ISyntaxVisitorShape<'Visitor,'Result>
        and 'VisitorShape : struct

    abstract Span: 'Syntax -> Span

and ISyntaxVisitorShape<'Visitor,'Result> =
    inherit IShape
    abstract VisitName: visitor: 'Visitor byref * syntax: Name * result: 'Result outref -> bool
    abstract VisitStringLiteral: visitor: 'Visitor byref * syntax: StringLiteral * result: 'Result outref -> bool
    abstract VisitLiteral: visitor: 'Visitor byref * syntax: Literal * result: 'Result outref -> bool
    abstract VisitToken: visitor: 'Visitor byref * kind: TokenKind * trivia: Trivia * result: 'Result outref -> bool

    abstract VisitWithSpan: syntaxShape: The<'SyntaxShape> * visitor: 'Visitor byref * syntax: 'Syntax * span: Span * result: 'Result outref -> bool
        when 'SyntaxShape :> ISyntaxShape<'Syntax>
        and 'SyntaxShape : struct

    abstract Visit: syntaxShape: The<'SyntaxShape> * visitor: 'Visitor byref * syntax: 'Syntax * result: 'Result outref -> bool
        when 'SyntaxShape :> ISyntaxShape<'Syntax>
        and 'SyntaxShape : struct

module SyntaxVisitor =
    let visit (_visitorShape: The<#ISyntaxVisitorShape<_,_>>) _syntaxShape (visitor: _ byref) syntax (result: _ outref) =
        Shape.instance(_visitorShape).Visit(_syntaxShape, &visitor, syntax, &result)

    let visitWithSpan (_visitorShape: The<#ISyntaxVisitorShape<_,_>>) _syntaxShape (visitor: _ byref) syntax span (result: _ outref) =
        Shape.instance(_visitorShape).VisitWithSpan(_syntaxShape, &visitor, syntax, span, &result)

    let visitToken (_visitorShape: The<#ISyntaxVisitorShape<_,_>>) (visitor: _ byref) kind trivia (result: _ outref) =
        Shape.instance(_visitorShape).VisitToken(&visitor, kind, trivia, &result)

    let visitName (_visitorShape: The<#ISyntaxVisitorShape<_,_>>) (visitor: _ byref) syntax (result: _ outref) =
        Shape.instance(_visitorShape).VisitName(&visitor, syntax, &result)

    let visitLiteral (_visitorShape: The<#ISyntaxVisitorShape<_,_>>) (visitor: _ byref) syntax (result: _ outref) =
        Shape.instance(_visitorShape).VisitLiteral(&visitor, syntax, &result)

    let visitStringLiteral (_visitorShape: The<#ISyntaxVisitorShape<_,_>>) (visitor: _ byref) syntax (result: _ outref) =
        Shape.instance(_visitorShape).VisitStringLiteral(&visitor, syntax, &result)

module Syntax =
    let enumerateChildren (_syntaxShape: The<#ISyntaxShape<_>>) _visitorShape (visitor: _ byref) syntax (result: _ outref) =
        Shape.instance(_syntaxShape).EnumerateChildren(_visitorShape, &visitor, syntax, &result)

    let enumerateChildrenReverse (_syntaxShape: The<#ISyntaxShape<_>>) _visitorShape (visitor: _ byref) syntax (result: _ outref) =
        Shape.instance(_syntaxShape).EnumerateChildrenReverse(_visitorShape, &visitor, syntax, &result)

    let span (_syntaxShape: The<#ISyntaxShape<_>>) x =
        Shape.instance(_syntaxShape).Span x

    type private FindFirstTrivia = struct
        interface ISyntaxVisitorShape<HEmpty, Trivia> with
            override _.VisitLiteral(_, x, r) = r <- x.trivia; true
            override _.VisitStringLiteral(_, StringLiteral x, r) = r <- x.trivia; true
            override _.VisitName(_, Name x, r) = r <- x.trivia; true
            override _.VisitToken(_, _, x, r) = r <- x; true
            override _.Visit(_s, v, x, r) = enumerateChildren _s the<FindFirstTrivia> &v x &r
            override _.VisitWithSpan(_s, v, x, _, r) = enumerateChildren _s the<FindFirstTrivia> &v x &r
    end

    type private FindLastTrivia = struct
        interface ISyntaxVisitorShape<HEmpty, Trivia> with
            override _.VisitLiteral(_, x, r) = r <- x.trivia; true
            override _.VisitStringLiteral(_, StringLiteral x, r) = r <- x.trivia; true
            override _.VisitName(_, Name x, r) = r <- x.trivia; true
            override _.VisitToken(_, _, x, r) = r <- x; true
            override _.Visit(_s, v, x, r) = enumerateChildrenReverse _s the<FindLastTrivia> &v x &r
            override _.VisitWithSpan(_s, v, x, _, r) = enumerateChildrenReverse _s the<FindLastTrivia> &v x &r
    end

    let firstTrivia _syntaxShape syntax =
        let mutable s = HEmpty
        let mutable r = Unchecked.defaultof<_>
        if enumerateChildren _syntaxShape the<FindFirstTrivia> &s syntax &r
        then ValueSome r
        else ValueNone

    let lastTrivia _syntaxShape syntax =
        let mutable s = HEmpty
        let mutable r = Unchecked.defaultof<_>
        if enumerateChildrenReverse _syntaxShape the<FindLastTrivia> &s syntax &r
        then ValueSome r
        else ValueNone

    type private FindFirstSpan = struct
        interface ISyntaxVisitorShape<HEmpty, Span> with
            member _.VisitName(_, Name x, r) = r <- x.trivia.span; true
            member _.VisitStringLiteral(_, StringLiteral x, r) = r <- x.trivia.span; true
            member _.VisitToken(_, _, x, r) = r <- x.span; true
            member _.VisitLiteral(_, x, r) = r <- x.trivia.span; true
            member _.VisitWithSpan(_, _, _, x, r) = r <- x; true
            member _.Visit(s, v, x, r) = enumerateChildren s the<FindFirstSpan> &v x &r
    end
    let private firstSpanFromDescendants _syntaxShape syntax =
        let mutable s = HEmpty
        let mutable r = Unchecked.defaultof<_>
        if enumerateChildren _syntaxShape the<FindFirstSpan> &s syntax &r then r
        else Span.empty

    type private FindLastSpan = struct
        interface ISyntaxVisitorShape<HEmpty, Span> with
            member _.VisitName(_, Name x, r) = r <- x.trivia.span; true
            member _.VisitStringLiteral(_, StringLiteral x, r) = r <- x.trivia.span; true
            member _.VisitToken(_, _, x, r) = r <- x.span; true
            member _.VisitLiteral(_, x, r) = r <- x.trivia.span; true
            member _.VisitWithSpan(_, _, _, x, r) = r <- x; true
            member _.Visit(s, v, x, r) = enumerateChildrenReverse s the<FindLastSpan> &v x &r
    end
    let private lastSpanFromDescendants _syntaxShape syntax =
        let mutable s = HEmpty
        let mutable r = Unchecked.defaultof<_>
        if enumerateChildrenReverse _syntaxShape the<FindLastSpan> &s syntax &r then r
        else Span.empty

    let mergeChildrenSpan _syntaxShape syntax =
        let first = firstSpanFromDescendants _syntaxShape syntax
        let last = lastSpanFromDescendants _syntaxShape syntax
        Span.merge first last

    let option (_: 'SomeValueIsSyntax The) = the<OptionIsSyntax<_,'SomeValueIsSyntax>>
    let list (_: 'ElementIsSyntax The) = the<ListIsSyntax<_,'ElementIsSyntax>>
    let sepBy (_: 'ElementIsSyntax The) = the<SepByIsSyntax<_,_,'ElementIsSyntax>>
    let triviaToken (_: 'KindIsSyntax The) = the<TriviaTokenIsSyntax<_,'KindIsSyntax>>
    let token (_: 'KindIsSyntax The) = the<SpanTokenIsSyntax<_,'KindIsSyntax>>
    let name = the<NameIsSyntax>
    let nameList = token (sepBy name)

    let fieldSep = the<FieldSepIsSyntax>
    let field = token the<FieldIsSyntax>
    let fieldList = the<FieldListIsSyntax>
    let tableConstructor = token the<TableConstructorIsSyntax>
    let args = token the<ArgsIsSyntax>
    let functionCall = token the<FunctionCallIsSyntax>
    let prefixExp = token the<PrefixExpIsSyntax>
    let var = token the<VarIsSyntax>
    let varList = token (sepBy var)
    let exp = token the<ExpIsSyntax>
    let expList = token (sepBy exp)
    let funcName = token the<FuncNameIsSyntax>
    let parameterList = token the<ParameterListIsSyntax>
    let stat = token the<StatIsSyntax>
    let lastStat = the<LastStatIsSyntax>
    let block = triviaToken the<BlockIsSyntax>
    let funcBody = token the<FuncBodyIsSyntax>

module SyntaxShapes =
    let inline private the' (_: 'T) = the<'T>

    type SpanTokenIsSyntax<'Kind,'KindIsSyntax> when 'KindIsSyntax :> ISyntaxShape<'Kind> and 'KindIsSyntax : struct = struct
        interface ISyntaxShape<Token<'Kind, Span>> with
            member _.EnumerateChildren(vs, v, x, r) = visitWithSpan vs the<'KindIsSyntax> &v x.kind x.trivia &r
            member _.EnumerateChildrenReverse(vs, v, x, r) = visitWithSpan vs the<'KindIsSyntax> &v x.kind x.trivia &r
            member _.Span x = x.trivia
    end

    type TriviaTokenIsSyntax<'Kind,'KindIsSyntax> when 'KindIsSyntax :> ISyntaxShape<'Kind> and 'KindIsSyntax : struct = struct
        interface ISyntaxShape<Token<'Kind, Trivia>> with
            member _.EnumerateChildren(vs, v, x, r) = visitWithSpan vs the<'KindIsSyntax> &v x.kind x.trivia.span &r
            member _.EnumerateChildrenReverse(vs, v, x, r) = visitWithSpan vs the<'KindIsSyntax> &v x.kind x.trivia.span &r
            member _.Span x = x.trivia.span
    end

    type NameIsSyntax = struct
        interface ISyntaxShape<Name> with
            member _.EnumerateChildren(vs, v, x, r) = visitName vs &v x &r
            member _.EnumerateChildrenReverse(vs, v, x, r) = visitName vs &v x &r
            member _.Span(Name x) = x.trivia.span
    end

    type OptionIsSyntax<'T,'S> when 'S :> ISyntaxShape<'T> and 'S : struct = struct
        interface ISyntaxShape<'T option> with
            override _.EnumerateChildren(vs, v, x, r) =
                match x with
                | Some x -> visit vs the<'S> &v x &r
                | _ -> false

            override _.EnumerateChildrenReverse(vs, v, x, r) =
                match x with
                | Some x -> visit vs the<'S> &v x &r
                | _ -> false

            override _.Span x =
                match x with
                | None -> Span.empty
                | Some x -> Syntax.span the<'S> x
    end

    type ListIsSyntax<'T,'S> when 'S :> ISyntaxShape<'T> and 'S : struct = struct
        interface ISyntaxShape<'T list> with
            member _.Span xs =
                match xs with
                | [] -> Span.empty
                | [x] -> Syntax.span the<'S> x
                | _ -> Span.merge (Syntax.span the<'S> (List.head xs)) (Syntax.span the<'S> (List.last xs))

            member _.EnumerateChildren(vs, v, xs, r) =
                let mutable find = false
                let mutable remaining = xs
                while
                    match remaining with
                    | [] -> false
                    | x::xs ->
                        find <- visit vs the<'S> &v x &r
                        remaining <- xs
                        not find
                    do ()
                find

            member _.EnumerateChildrenReverse(vs, v, xs, r) =
                match xs with
                | [] -> false
                | [x] -> visit vs the<'S> &v x &r
                | _ ->
                    // TODO: pool
                    let buffer = ResizeArray()
                    for x in xs do buffer.Add x

                    let mutable find = false
                    let mutable i = buffer.Count-1
                    while 0 <= i && (find <- visit vs the<'S> &v buffer.[i] &r; not find) do
                        i <- i - 1
                    find
    end

    type SepByIsSyntax<'Sep,'T,'S> when 'S :> ISyntaxShape<'T> and 'S : struct = struct
        interface ISyntaxShape<SepBy<'Sep,'T>> with
            member _.Span(SepBy(x1, sepXs)) =
                let s1 = Syntax.span the<'S> x1
                match sepXs with
                | [] -> s1
                | _ ->
                    let (_, x2) = List.last sepXs
                    Span.merge s1 (Syntax.span the<'S> x2)

            member _.EnumerateChildren(vs, v, SepBy(x, sepXs), r) =
                if visit vs the<'S> &v x &r then true else

                let mutable find = false
                let mutable remaining = sepXs
                while
                    match remaining with
                    | [] -> false
                    | (_, x)::sepXs ->
                        find <- visit vs the<'S> &v x &r
                        remaining <- sepXs
                        not find
                    do ()
                find

            member _.EnumerateChildrenReverse(vs, v, SepBy(x1, sepXs) & xs, r) =
                match sepXs with
                | [] -> visit vs the<'S> &v x1 &r
                | [_,x2] ->
                    visit vs the<'S> &v x2 &r ||
                    visit vs the<'S> &v x1 &r

                | _ ->
                    // TODO: pool
                    let buffer = ResizeArray()
                    SepBy.appendToResizeArray xs buffer

                    let mutable find = false
                    let mutable i = buffer.Count-1
                    while 0 <= i && (find <- visit vs the<'S> &v buffer.[i] &r; not find) do
                        i <- i - 1
                    find
    end

    type ExpIsSyntax = struct
        interface ISyntaxShape<Exp'> with
            member _s.Span x = Syntax.mergeChildrenSpan (the' _s) x

            member _.EnumerateChildren(vs, v, x, r) =
                match x with
                | Literal x -> visitLiteral vs &v x &r
                | VarArg x -> visitToken vs &v K.Dot3 x.trivia &r
                | Function(x1, x2) ->
                    visitToken vs &v K.Function x1.trivia &r ||
                    visit vs Syntax.funcBody &v x2 &r

                | PrefixExp x -> visit vs Syntax.prefixExp &v x &r
                | NewTable x -> visit vs Syntax.tableConstructor &v x &r
                | Binary(x1, x2, x3) ->
                    visit vs Syntax.exp &v x1 &r ||
                    visitToken vs &v (TokenKind.ofBinaryOpKind x2.kind) x2.trivia &r ||
                    visit vs Syntax.exp &v x3 &r

                | Unary(x1, x2) ->
                    visitToken vs &v (TokenKind.ofUnaryOpKind x1.kind) x1.trivia &r ||
                    visit vs Syntax.exp &v x2 &r

            member _.EnumerateChildrenReverse(vs, v, x, r) =
                match x with
                | Literal x -> visitLiteral vs &v x &r
                | VarArg x -> visitToken vs &v K.Dot3 x.trivia &r
                | Function(x1, x2) ->
                    visit vs Syntax.funcBody &v x2 &r ||
                    visitToken vs &v K.Function x1.trivia &r

                | PrefixExp x -> visit vs Syntax.prefixExp &v x &r
                | NewTable x -> visit vs Syntax.tableConstructor &v x &r
                | Binary(x1, x2, x3) ->
                    visit vs Syntax.exp &v x3 &r ||
                    visitToken vs &v (TokenKind.ofBinaryOpKind x2.kind) x2.trivia &r ||
                    visit vs Syntax.exp &v x1 &r

                | Unary(x1, x2) ->
                    visit vs Syntax.exp &v x2 &r ||
                    visitToken vs &v (TokenKind.ofUnaryOpKind x1.kind) x1.trivia &r
    end

    type ArgsIsSyntax = struct
        interface ISyntaxShape<Args'> with
            member _s.Span x = Syntax.mergeChildrenSpan (the' _s) x
            member _.EnumerateChildren(vs, v, x, r) =
                match x with
                | StringArg x -> visitStringLiteral vs &v x &r
                | Args(x1, x2, x3) ->
                    visitToken vs &v K.LBracket x1.trivia &r ||
                    visit vs (Syntax.option Syntax.expList) &v x2 &r ||
                    visitToken vs &v K.RBracket x3.trivia &r

                | TableArg x -> visit vs Syntax.tableConstructor &v x &r

            member _.EnumerateChildrenReverse(vs, v, x, r) =
                match x with
                | StringArg x -> visitStringLiteral vs &v x &r
                | Args(x1, x2, x3) ->
                    visitToken vs &v K.RBracket x3.trivia &r ||
                    visit vs (Syntax.option Syntax.expList) &v x2 &r ||
                    visitToken vs &v K.LBracket x1.trivia &r

                | TableArg x -> visit vs Syntax.tableConstructor &v x &r
    end

    type FunctionCallIsSyntax = struct
        interface ISyntaxShape<FunctionCall'> with
            member _s.Span x = Syntax.mergeChildrenSpan (the' _s) x

            member _.EnumerateChildren(vs, v, x, r) =
                match x with
                | Call(x1, x2) ->
                    visit vs Syntax.prefixExp &v x1 &r ||
                    visit vs Syntax.args &v x2 &r

                | CallWithSelf(x1, x2, x3, x4) ->
                    visit vs Syntax.prefixExp &v x1 &r ||
                    visitToken vs &v K.Colon x2.trivia &r ||
                    visitName vs &v x3 &r ||
                    visit vs Syntax.args &v x4 &r

            member _.EnumerateChildrenReverse(vs, v, x, r) =
                match x with
                | Call(x1, x2) ->
                    visit vs Syntax.args &v x2 &r ||
                    visit vs Syntax.prefixExp &v x1 &r

                | CallWithSelf(x1, x2, x3, x4) ->
                    visit vs Syntax.args &v x4 &r ||
                    visitName vs &v x3 &r ||
                    visitToken vs &v K.Colon x2.trivia &r ||
                    visit vs Syntax.prefixExp &v x1 &r
    end

    type PrefixExpIsSyntax = struct
        interface ISyntaxShape<PrefixExp'> with
            member s.Span x = Syntax.mergeChildrenSpan (the' s) x

            member _.EnumerateChildren(vs, v, x, r) =
                match x with
                | Var x -> visit vs Syntax.var &v x &r
                | Apply x -> visit vs Syntax.functionCall &v x &r
                | Wrap(x1, x2, x3) ->
                    visitToken vs &v K.LBracket x1.trivia &r ||
                    visit vs Syntax.exp &v x2 &r ||
                    visitToken vs &v K.RBracket x3.trivia &r

            member _.EnumerateChildrenReverse(vs, v, x, r) =
                match x with
                | Var x -> visit vs Syntax.var &v x &r
                | Apply x -> visit vs Syntax.functionCall &v x &r
                | Wrap(x1, x2, x3) ->
                    visitToken vs &v K.RBracket x3.trivia &r ||
                    visit vs Syntax.exp &v x2 &r ||
                    visitToken vs &v K.LBracket x1.trivia &r
    end

    type VarIsSyntax = struct
        interface ISyntaxShape<Var'> with
            member s.Span x = Syntax.mergeChildrenSpan (the' s) x

            member _.EnumerateChildren(vs, v, x, r) =
                match x with
                | Variable x -> visitName vs &v x &r
                | Index(x1, x2, x3, x4) ->
                    visit vs Syntax.prefixExp &v x1 &r ||
                    visitToken vs &v K.LSBracket x2.trivia &r ||
                    visit vs Syntax.exp &v x3 &r ||
                    visitToken vs &v K.RSBracket x4.trivia &r

                | Member(x1, x2, x3) ->
                    visit vs Syntax.prefixExp &v x1 &r ||
                    visitToken vs &v K.Dot x2.trivia &r ||
                    visitName vs &v x3 &r

            member _.EnumerateChildrenReverse(vs, v, x, r) =
                match x with
                | Variable x -> visitName vs &v x &r
                | Index(x1, x2, x3, x4) ->
                    visitToken vs &v K.RSBracket x4.trivia &r ||
                    visit vs Syntax.exp &v x3 &r ||
                    visitToken vs &v K.LSBracket x2.trivia &r ||
                    visit vs Syntax.prefixExp &v x1 &r

                | Member(x1, x2, x3) ->
                    visitName vs &v x3 &r ||
                    visitToken vs &v K.Dot x2.trivia &r ||
                    visit vs Syntax.prefixExp &v x1 &r
    end

    type FieldSepIsSyntax = struct
        interface ISyntaxShape<FieldSep> with
            member _.Span x = x.trivia.span
            member _.EnumerateChildren(vs, v, x, r) = visitToken vs &v (TokenKind.ofFieldSepKind x.kind) x.trivia &r
            member _.EnumerateChildrenReverse(vs, v, x, r) = visitToken vs &v (TokenKind.ofFieldSepKind x.kind) x.trivia &r
    end

    type FieldIsSyntax = struct
        interface ISyntaxShape<Field'> with
            member s.Span x = Syntax.mergeChildrenSpan (the' s) x

            member _.EnumerateChildren(vs, v, x, r) =
                match x with
                | Init x -> visit vs Syntax.exp &v x &r
                | MemberInit(x1, x2, x3) ->
                    visitName vs &v x1 &r ||
                    visitToken vs &v K.Eq x2.trivia &r ||
                    visit vs Syntax.exp &v x3 &r

                | IndexInit(x1, x2, x3, x4, x5) ->
                    visitToken vs &v K.LSBracket x1.trivia &r ||
                    visit vs Syntax.exp &v x2 &r ||
                    visitToken vs &v K.RSBracket x3.trivia &r ||
                    visitToken vs &v K.Eq x4.trivia &r ||
                    visit vs Syntax.exp &v x5 &r

            member _.EnumerateChildrenReverse(vs, v, x, r) =
                match x with
                | Init x -> visit vs Syntax.exp &v x &r
                | MemberInit(x1, x2, x3) ->
                    visit vs Syntax.exp &v x3 &r ||
                    visitToken vs &v K.Eq x2.trivia &r ||
                    visitName vs &v x1 &r

                | IndexInit(x1, x2, x3, x4, x5) ->
                    visit vs Syntax.exp &v x5 &r ||
                    visitToken vs &v K.Eq x4.trivia &r ||
                    visitToken vs &v K.RSBracket x3.trivia &r ||
                    visit vs Syntax.exp &v x2 &r ||
                    visitToken vs &v K.LSBracket x1.trivia &r
    end

    type FieldListIsSyntax = struct
        interface ISyntaxShape<FieldList> with
            member _s.Span x = Syntax.mergeChildrenSpan (the' _s) x

            member _.EnumerateChildren(vs, v, FieldList(x1, x2), r) =
                visit vs (Syntax.sepBy Syntax.field) &v x1 &r ||
                visit vs (Syntax.option Syntax.fieldSep) &v x2 &r

            member _.EnumerateChildrenReverse(vs, v, FieldList(x1, x2), r) =
                visit vs (Syntax.option Syntax.fieldSep) &v x2 &r ||
                visit vs (Syntax.sepBy Syntax.field) &v x1 &r
    end

    type TableConstructorIsSyntax = struct
        interface ISyntaxShape<TableConstructor'> with
            member s.Span x = Syntax.mergeChildrenSpan (the' s) x

            member _.EnumerateChildren(vs, v, TableConstructor(x1, x2, x3), r) =
                visitToken vs &v K.LCBracket x1.trivia &r ||
                visit vs (Syntax.option Syntax.fieldList) &v x2 &r ||
                visitToken vs &v K.RCBracket x3.trivia &r

            member _.EnumerateChildrenReverse(vs, v, TableConstructor(x1, x2, x3), r) =
                visitToken vs &v K.RCBracket x3.trivia &r ||
                visit vs (Syntax.option Syntax.fieldList) &v x2 &r ||
                visitToken vs &v K.LCBracket x1.trivia &r
    end

    type ParameterListIsSyntax = struct
        interface ISyntaxShape<ParameterList'> with
            member s.Span x = Syntax.mergeChildrenSpan (the' s) x

            member _.EnumerateChildren(vs, v, x, r) =
                match x with
                | VarParameter x -> visitToken vs &v K.Dot3 x.trivia &r
                | ParameterList(x1, x2) ->
                    visit vs Syntax.nameList &v x1 &r || (
                        match x2 with
                        | None -> false
                        | Some(t1, t2) ->
                            visitToken vs &v K.Comma t1.trivia &r ||
                            visitToken vs &v K.Dot3 t2.trivia &r
                    )

            member _.EnumerateChildrenReverse(vs, v, x, r) =
                match x with
                | VarParameter x -> visitToken vs &v K.Dot3 x.trivia &r
                | ParameterList(x1, x2) ->
                    (
                        match x2 with
                        | None -> false
                        | Some(t1, t2) ->
                            visitToken vs &v K.Dot3 t2.trivia &r ||
                            visitToken vs &v K.Comma t1.trivia &r
                    ) ||
                    visit vs Syntax.nameList &v x1 &r
    end

    type DotNameIsSyntax = struct
        interface ISyntaxShape<Token * Name> with
            member s.Span x = Syntax.mergeChildrenSpan (the' s) x

            member _.EnumerateChildren(vs, v, (x1, x2), r) =
                visitToken vs &v K.Dot x1.trivia &r ||
                visitName vs &v x2 &r

            member _.EnumerateChildrenReverse(vs, v, (x1, x2), r) =
                visitName vs &v x2 &r ||
                visitToken vs &v K.Dot x1.trivia &r
    end

    type FuncNameIsSyntax = struct
        interface ISyntaxShape<FuncName'> with
            member s.Span x = Syntax.mergeChildrenSpan (the' s) x

            member _.EnumerateChildren(vs, v, FuncName(x1, x2, x3), r) =
                visitName vs &v x1 &r ||
                visit vs (Syntax.list the<DotNameIsSyntax>) &v x2 &r ||
                visit vs (Syntax.option the<DotNameIsSyntax>) &v x3 &r

            member _.EnumerateChildrenReverse(vs, v, FuncName(x1, x2, x3), r) =
                visit vs (Syntax.option the<DotNameIsSyntax>) &v x3 &r ||
                visit vs (Syntax.list the<DotNameIsSyntax>) &v x2 &r ||
                visitName vs &v x1 &r
    end

    type ElseIfIsSyntax = struct
        interface ISyntaxShape<ElseIf'> with
            member s.Span x = Syntax.mergeChildrenSpan (the' s) x

            member _.EnumerateChildren(vs, v, ElseIf(x1, x2, x3, x4), r) =
                visitToken vs &v K.ElseIf x1.trivia &r ||
                visit vs Syntax.exp &v x2 &r ||
                visitToken vs &v K.Then x3.trivia &r ||
                visit vs Syntax.block &v x4 &r

            member _.EnumerateChildrenReverse(vs, v, ElseIf(x1, x2, x3, x4), r) =
                visit vs Syntax.block &v x4 &r ||
                visitToken vs &v K.Then x3.trivia &r ||
                visit vs Syntax.exp &v x2 &r ||
                visitToken vs &v K.ElseIf x1.trivia &r
    end

    type ElseIsSyntax = struct
        interface ISyntaxShape<Else'> with
            member s.Span x = Syntax.mergeChildrenSpan (the' s) x

            member _.EnumerateChildren(vs, v, Else(x1, x2), r) =
                visitToken vs &v K.Else x1.trivia &r ||
                visit vs Syntax.block &v x2 &r

            member _.EnumerateChildrenReverse(vs, v, Else(x1, x2), r) =
                visit vs Syntax.block &v x2 &r ||
                visitToken vs &v K.Else x1.trivia &r
    end

    type StatIsSyntax = struct
        interface ISyntaxShape<Stat'> with
            member s.Span x = Syntax.mergeChildrenSpan (the' s) x

            member _.EnumerateChildren(vs, v, x, r) =
                match x with
                | FunctionCall x -> visit vs Syntax.functionCall &v x &r
                | Assign(x1, x2, x3) ->
                    visit vs Syntax.varList &v x1 &r ||
                    visitToken vs &v K.Eq x2.trivia &r ||
                    visit vs Syntax.expList &v x3 &r

                | Do(x1, x2, x3) ->
                    visitToken vs &v K.Do x1.trivia &r ||
                    visit vs Syntax.block &v x2 &r ||
                    visitToken vs &v K.End x3.trivia &r

                | While(x1, x2, x3, x4, x5) ->
                    visitToken vs &v K.While x1.trivia &r ||
                    visit vs Syntax.exp &v x2 &r ||
                    visitToken vs &v K.Do x3.trivia &r ||
                    visit vs Syntax.block &v x4 &r ||
                    visitToken vs &v K.End x5.trivia &r

                | RepeatUntil(x1, x2, x3, x4) ->
                    visitToken vs &v K.Repeat x1.trivia &r ||
                    visit vs Syntax.block &v x2 &r ||
                    visitToken vs &v K.Until x3.trivia &r ||
                    visit vs Syntax.exp &v x4 &r

                | If(x1, x2, x3, x4, x5, x6, x7) ->
                    visitToken vs &v K.If x1.trivia &r ||
                    visit vs Syntax.exp &v x2 &r ||
                    visitToken vs &v K.Then x3.trivia &r ||
                    visit vs Syntax.block &v x4 &r ||
                    visit vs (Syntax.list (Syntax.token the<ElseIfIsSyntax>)) &v x5 &r ||
                    visit vs (Syntax.option (Syntax.token the<ElseIsSyntax>)) &v x6 &r ||
                    visitToken vs &v K.End x7.trivia &r

                | For(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) ->
                    visitToken vs &v K.For x1.trivia &r ||
                    visitName vs &v x2 &r ||
                    visitToken vs &v K.Eq x3.trivia &r ||
                    visit vs Syntax.exp &v x4 &r ||
                    visitToken vs &v K.Colon x5.trivia &r ||
                    visit vs Syntax.exp &v x6 &r || (
                        match x7 with
                        | None -> false
                        | Some(x7, x7') ->
                            visitToken vs &v K.Comma x7.trivia &r ||
                            visit vs Syntax.exp &v x7' &r
                    ) ||
                    visitToken vs &v K.Do x8.trivia &r ||
                    visit vs Syntax.block &v x9 &r ||
                    visitToken vs &v K.End x10.trivia &r

                | ForIn(x1, x2, x3, x4, x5, x6, x7) ->
                    visitToken vs &v K.For x1.trivia &r ||
                    visit vs Syntax.nameList &v x2 &r ||
                    visitToken vs &v K.In x3.trivia &r ||
                    visit vs Syntax.expList &v x4 &r ||
                    visitToken vs &v K.Do x5.trivia &r ||
                    visit vs Syntax.block &v x6 &r ||
                    visitToken vs &v K.End x7.trivia &r

                | FunctionDecl(x1, x2, x3) ->
                    visitToken vs &v K.Function x1.trivia &r ||
                    visit vs Syntax.funcName &v x2 &r ||
                    visit vs Syntax.funcBody &v x3 &r

                | LocalFunction(x1, x2, x3, x4) ->
                    visitToken vs &v K.Local x1.trivia &r ||
                    visitToken vs &v K.Function x2.trivia &r ||
                    visitName vs &v x3 &r ||
                    visit vs Syntax.funcBody &v x4 &r

                | Local(x1, x2, x3) ->
                    visitToken vs &v K.Local x1.trivia &r ||
                    visit vs Syntax.nameList &v x2 &r || (
                        match x3 with
                        | None -> false
                        | Some(x3, x3') ->
                            visitToken vs &v K.Eq x3.trivia &r ||
                            visit vs Syntax.expList &v x3' &r
                    )

            member _.EnumerateChildrenReverse(vs, v, x, r) =
                match x with
                | FunctionCall x -> visit vs Syntax.functionCall &v x &r
                | Assign(x1, x2, x3) ->
                    visit vs Syntax.expList &v x3 &r ||
                    visitToken vs &v K.Eq x2.trivia &r ||
                    visit vs Syntax.varList &v x1 &r

                | Do(x1, x2, x3) ->
                    visitToken vs &v K.End x3.trivia &r ||
                    visit vs Syntax.block &v x2 &r ||
                    visitToken vs &v K.Do x1.trivia &r

                | While(x1, x2, x3, x4, x5) ->
                    visitToken vs &v K.End x5.trivia &r ||
                    visit vs Syntax.block &v x4 &r ||
                    visitToken vs &v K.Do x3.trivia &r ||
                    visit vs Syntax.exp &v x2 &r ||
                    visitToken vs &v K.While x1.trivia &r

                | RepeatUntil(x1, x2, x3, x4) ->
                    visit vs Syntax.exp &v x4 &r ||
                    visitToken vs &v K.Until x3.trivia &r ||
                    visit vs Syntax.block &v x2 &r ||
                    visitToken vs &v K.Repeat x1.trivia &r

                | If(x1, x2, x3, x4, x5, x6, x7) ->
                    visitToken vs &v K.End x7.trivia &r ||
                    visit vs (Syntax.option (Syntax.token the<ElseIsSyntax>)) &v x6 &r ||
                    visit vs (Syntax.list (Syntax.token the<ElseIfIsSyntax>)) &v x5 &r ||
                    visit vs Syntax.block &v x4 &r ||
                    visitToken vs &v K.Then x3.trivia &r ||
                    visit vs Syntax.exp &v x2 &r ||
                    visitToken vs &v K.If x1.trivia &r

                | For(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) ->
                    visitToken vs &v K.End x10.trivia &r ||
                    visit vs Syntax.block &v x9 &r ||
                    visitToken vs &v K.Do x8.trivia &r || (
                        match x7 with
                        | None -> false
                        | Some(x7, x7') ->
                            visit vs Syntax.exp &v x7' &r ||
                            visitToken vs &v K.Comma x7.trivia &r
                    ) ||
                    visit vs Syntax.exp &v x6 &r || 
                    visitToken vs &v K.Colon x5.trivia &r ||
                    visit vs Syntax.exp &v x4 &r ||
                    visitToken vs &v K.Eq x3.trivia &r ||
                    visitName vs &v x2 &r ||
                    visitToken vs &v K.For x1.trivia &r

                | ForIn(x1, x2, x3, x4, x5, x6, x7) ->
                    visitToken vs &v K.End x7.trivia &r ||
                    visit vs Syntax.block &v x6 &r ||
                    visitToken vs &v K.Do x5.trivia &r ||
                    visit vs Syntax.expList &v x4 &r ||
                    visitToken vs &v K.In x3.trivia &r ||
                    visit vs Syntax.nameList &v x2 &r ||
                    visitToken vs &v K.For x1.trivia &r

                | FunctionDecl(x1, x2, x3) ->
                    visit vs Syntax.funcBody &v x3 &r ||
                    visit vs Syntax.funcName &v x2 &r ||
                    visitToken vs &v K.Function x1.trivia &r

                | LocalFunction(x1, x2, x3, x4) ->
                    visit vs Syntax.funcBody &v x4 &r ||
                    visitName vs &v x3 &r ||
                    visitToken vs &v K.Function x2.trivia &r ||
                    visitToken vs &v K.Local x1.trivia &r

                | Local(x1, x2, x3) ->
                    (
                        match x3 with
                        | None -> false
                        | Some(x3, x3') ->
                            visit vs Syntax.expList &v x3' &r ||
                            visitToken vs &v K.Eq x3.trivia &r
                    ) ||
                    visit vs Syntax.nameList &v x2 &r ||
                    visitToken vs &v K.Local x1.trivia &r
    end

    type LastStatIsSyntax = struct
        interface ISyntaxShape<LastStat * Token option> with
            override s.Span x = Syntax.mergeChildrenSpan (the' s) x

            override _.EnumerateChildren(vs, v, (x1, x2), r) =
                (
                    match x1.kind with
                    | Break x -> visitToken vs &v K.Break x.trivia &r
                    | Return(x1, x2) ->
                        visitToken vs &v K.Return x1.trivia &r ||
                        visit vs (Syntax.option Syntax.expList) &v x2 &r
                ) ||
                (
                    match x2 with
                    | Some x2 -> visitToken vs &v K.Semicolon x2.trivia &r
                    | _ -> false
                )

            override _.EnumerateChildrenReverse(vs, v, (x1, x2), r) =
                (
                    match x2 with
                    | Some x2 -> visitToken vs &v K.Semicolon x2.trivia &r
                    | _ -> false
                ) ||
                (
                    match x1.kind with
                    | Break x -> visitToken vs &v K.Break x.trivia &r
                    | Return(x1, x2) ->
                        visit vs (Syntax.option Syntax.expList) &v x2 &r ||
                        visitToken vs &v K.Return x1.trivia &r
                ) 
    end

    type BlockStatIsSyntax = struct
        interface ISyntaxShape<Stat * Token option> with
            member s.Span x = Syntax.mergeChildrenSpan (the' s) x

            member _.EnumerateChildren(vs, v, (x1, x2), r) =
                visit vs Syntax.stat &v x1 &r || (
                    match x2 with
                    | Some x2 -> visitToken vs &v K.Semicolon x2.trivia &r
                    | _ -> false
                )

            member _.EnumerateChildrenReverse(vs, v, (x1, x2), r) =
                (
                    match x2 with
                    | Some x2 -> visitToken vs &v K.Semicolon x2.trivia &r
                    | _ -> false
                ) ||
                visit vs Syntax.stat &v x1 &r
    end

    type BlockIsSyntax = struct
        interface ISyntaxShape<Block'> with
            member s.Span x = Syntax.mergeChildrenSpan (the' s) x

            member _.EnumerateChildren(vs, v, x, r) =
                visit vs (Syntax.list the<BlockStatIsSyntax>) &v x.stats &r ||
                visit vs (Syntax.option Syntax.lastStat) &v x.lastStat &r

            member _.EnumerateChildrenReverse(vs, v, x, r) =
                visit vs (Syntax.option Syntax.lastStat) &v x.lastStat &r ||
                visit vs (Syntax.list the<BlockStatIsSyntax>) &v x.stats &r
    end

    type FuncBodyIsSyntax = struct
        interface ISyntaxShape<FuncBody'> with
            member s.Span x = Syntax.mergeChildrenSpan (the' s) x

            member _.EnumerateChildren(vs, v, FuncBody(x1, x2, x3, x4, x5), r) =
                visitToken vs &v K.LBracket x1.trivia &r ||
                visit vs (Syntax.option Syntax.parameterList) &v x2 &r ||
                visitToken vs &v K.RBracket x3.trivia &r ||
                visit vs Syntax.block &v x4 &r ||
                visitToken vs &v K.End x5.trivia &r

            member _.EnumerateChildrenReverse(vs, v, FuncBody(x1, x2, x3, x4, x5), r) =
                visitToken vs &v K.End x5.trivia &r ||
                visit vs Syntax.block &v x4 &r ||
                visitToken vs &v K.RBracket x3.trivia &r ||
                visit vs (Syntax.option Syntax.parameterList) &v x2 &r ||
                visitToken vs &v K.LBracket x1.trivia &r
    end
