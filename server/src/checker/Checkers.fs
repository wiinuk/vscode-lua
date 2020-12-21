module rec LuaChecker.Checkers
open LuaChecker
open LuaChecker.CheckerEnv
open LuaChecker.Syntax
open LuaChecker.Syntaxes
open LuaChecker.TypeSystem
open LuaChecker.Primitives
module T = LuaChecker.TypedSyntaxes
module D = LuaChecker.Syntax.Documents
type private I = LuaChecker.IdentifierKind
type private S = LuaChecker.IdentifierScope
type private R = LuaChecker.IdentifierRepresentation


[<AutoOpen>]
module private Helpers =
    let suppressDiagnostics suppress env =
        struct(
            env.rare.suppressDiagnostics,
            { env with rare = { env.rare with suppressDiagnostics = suppress } }
        )
    let inline modifyPackagePath env f = { env with rare = { env.rare with packagePath = f env.rare.packagePath } }
    let withSpan span x = { kind = x; trivia = span }

    let makeVar s k r n t = T.Var(s, k, r, n, t, ValueNone)
    let literal span t l = struct(withSpan span (T.Literal(l, t, ValueNone)), t)

    let unifyDiagnosticsAt env source t1 t2 =
        reportIfUnifyError env (Source.measure source) t1 t2

    let isStaticKey k =
        match k.kind with
        | Literal { kind = Nil } -> false
        | Literal _ -> true

        // TODO:
        | _ -> false

    let staticKey = function
        | { kind = Literal { kind = x } } ->
            match x with
            | Number x -> ValueSome <| FieldKey.Number x
            | String x -> ValueSome <| FieldKey.String x
            | True -> ValueSome <| FieldKey.Bool true
            | False -> ValueSome <| FieldKey.Bool false
            | _ -> ValueNone

        // TODO:
        | _ -> ValueNone

    let isStaticTrueLike = function
        | { kind = Literal { kind = True | Number _ | String _ } } -> true

        // TODO:
        | _ -> false

    let hasBreakInScope { kind = b } =
        List.exists (fst >> hasBreakInScopeAtStat) b.stats ||
        b.lastStat |> Option.exists (function { kind = Break _ }, _ -> true | _ -> false)

    let hasBreakInScopeAtStat x =
        match x.kind with
        | If(ifTrue = ifTrue; elseIfs = elseIfs; else' = ifFalse) ->
            hasBreakInScope ifTrue ||
            List.exists (fun { kind = ElseIf(ifTrue = b) } -> hasBreakInScope b) elseIfs ||
            Option.exists (fun { kind = Else(ifFalse = b) } -> hasBreakInScope b) ifFalse

        | Do(_, body, _) -> hasBreakInScope body

        | FunctionCall _
        | Assign _
        | While _
        | RepeatUntil _
        | For _
        | ForIn _
        | FunctionDecl _
        | LocalFunction _
        | Local _ -> false

    /// `while true do …(no available break)… end`
    let isInfinityLoop cond body = isStaticTrueLike cond && not <| hasBreakInScope body

    /// `var`
    let (|VarName|) = function
        | Var { kind = Variable name } -> ValueSome name
        | _ -> ValueNone

    // `require("…")`
    let (|RequireCall|_|) env = function
        | Call({ kind = VarName(ValueSome(Name { kind = f; trivia = ft } as fn)) }, args) ->
            match resolveVariable ft.span f env with
            | ValueSome { declarationFeatures = DeclarationFeatures.GlobalRequire } ->
                match args.kind with
                | StringArg(StringLiteral { kind = x; trivia = t })
                | Args(args = Some { kind = SepBy({ kind = Literal { kind = String x; trivia = t } }, []) }) ->
                    Some
                        {|
                            requireName = fn
                            moduleNameTrivia = t
                            moduleName = x
                        |}

                | Args _
                | TableArg _ -> None

            | _ -> None
        | _ -> None

    let (|StaticString|) = function
        | Literal { kind = String x } -> ValueSome x
        | _ -> ValueNone

    /// `this.member` or `this["member"]`
    let (|MemberAccess|) = function
        | Index(this, _, { kind = StaticString(ValueSome x) }, _)
        | Member(this, _, Name { kind = x }) -> ValueSome struct(this.kind, x)
        | _ -> ValueNone

    /// `package.path`
    let (|PackagePath|) env = function
        | MemberAccess(ValueSome(VarName(ValueSome(Name { kind = package; trivia = packageTrivia })), "path")) ->
            match resolveVariable packageTrivia.span package env with
            | ValueSome { declarationFeatures = DeclarationFeatures.GlobalPackage } -> true
            | _ -> false
        | _ -> false

    /// `package.path`
    let (|PackagePathExp|) env = function
        | PrefixExp { kind = Var { kind = PackagePath env x } } -> x
        | _ -> false

    /// `l .. r`
    let (|ConcatOp|) = function
        | Binary(l, { kind = Con }, r) -> ValueSome struct(l.kind, r.kind)
        | _ -> ValueNone

    /// `package.path = … package.path …`
    let (|StaticUpdatePackagePath|_|) env = function

        // package.path = …
        | struct(SepBy({ kind = PackagePath env true }, []), SepBy({ kind = update }, [])) ->
            match update with
            | ConcatOp(ValueSome(l, r)) ->
                match l, r with

                // s .. package.path
                | StaticString(ValueSome s), PackagePathExp env true -> Some(Some s, None)

                // package.path .. s
                | PackagePathExp env true, StaticString(ValueSome s) -> Some(None, Some s)

                // s1 .. package.path .. s2
                | ConcatOp(ValueSome(StaticString(ValueSome s1), PackagePathExp env true)), StaticString(ValueSome s2) -> Some(Some s1, Some s2)

                | _ -> None

            // package.path
            | PackagePathExp env true -> Some(None, None)

            | _ -> None
        | _ -> None

    let resolveModuleFile env moduleName =
        let filePath = env.rare.noUpdate.filePath |> DocumentPath.toUri
        let packagePaths = TopEnv.parseLuaPath env.rare.packagePath
        let moduleName = (moduleName: string).Replace('.', '/')

        let modulePaths =
            packagePaths
            |> List.map (fun packagePath ->
                let modulePath = packagePath.Replace("?", moduleName)
                DocumentPath.ofRelativeUri filePath (System.Uri(modulePath, System.UriKind.RelativeOrAbsolute))
            )

        let moduleFile =
            modulePaths
            |> List.tryPick (fun modulePath ->
                Project.tryFind modulePath (Local.get env.rare.noUpdate.project)
                |> ValueOption.map (fun x -> modulePath, x)
                |> VOption.box
            )

        match moduleFile with
        | Some f -> Ok f
        | _ -> Error modulePaths

    let mostSeriousDiagnostic e =
        e
        |> Seq.fold (fun mostImportant e ->
            match mostImportant, e with
            | ValueNone, _
            | ValueSome(Diagnostic(_, _, DiagnosticKind.ExternalModuleError _)), _ -> ValueSome e

            | ValueSome(Diagnostic(_, ms, _)), Diagnostic(_, s, _) ->
                if ms < s then ValueSome e else mostImportant

        ) ValueNone

    let parseAndCheckSource' visitedSources filePath source project =
        let struct(syntax, syntaxDiagnostics) = parse project.projectRare.fileSystem source
        let semantics, diagnostics, project = checkSyntaxAndCache' visitedSources project filePath source syntaxDiagnostics syntax
        semantics, diagnostics, project

    let checkSourceFileCached' visitedSources project filePath { source = source; stage = stage } =
        match stage with
        | BeforeParse ->
            parseAndCheckSource' visitedSources filePath source project

        | AnalysisComplete(s, es) ->
            s.typedTree, es, project

    let checkSyntaxAndCache' visitedSources project filePath source syntaxDiagnostics syntaxTree =
        let chunk, semanticsDiagnostics, project = chunk' project.projectRare.initialGlobal visitedSources project filePath source syntaxTree
        let e = Seq.cache <| Seq.append syntaxDiagnostics semanticsDiagnostics

        let s = {
            syntaxTree = syntaxTree
            typedTree = chunk
        }
        let sourceFile = { stage = AnalysisComplete(s, e); source = source }
        let project = Project.addSourceFileNoCheck filePath sourceFile project
        chunk, e, project

    let unify env t1 t2 = Type.unify (typeEnv env) t1 t2

    let (|@) x l = { kind = x; trivia = l }

    /// ?m...(?e: nil..)
    let nilOrUppers (TypeCache typeCache as env) l =
        newMultiVarTypeWith env TypeNames.multiRestNils (typeCache.nilOrUpperMultiElementConstraint |@ l) |@ l

    let multiType2 env l t1 t2 =
        let types = types env
        types.cons(t1, types.cons(t2, types.empty |@ l) |@ l) |@ l

    let multiType1 env t1 l = TypeSystem.multi1 (types env) t1 l

    /// (t, ?e...(?a: nil..))
    let multiType1AndNilOrUppers (Types types as env) t location =
        types.cons(t, nilOrUppers env location) |> Type.makeWithLocation location

    /// (t, ?m...)
    let multiType1AndAny (Types types as env) t location =
        types.cons(t, newMultiVarType env TypeNames.multiType1 |@ location) |@ location

    let multiTypeAsSingleType env span m =
        // unify `?m...` `(?t, ?r...)`
        let l = sourceLocation env span
        let t = newValueVarType env TypeNames.multiType1 |@ l
        reportIfUnifyError env span m (multiType1AndAny env t l)
        t

    let fetchSourceContents fs = function
        | InMemory(source, _) -> source
        | InFs(path, _) -> fs.readAllText path

    let inline modifyByCas (location: _ byref) f =
        while
            begin
                let x1 = location
                let x2 = f x1
                not (LanguagePrimitives.PhysicalEquality (System.Threading.Interlocked.CompareExchange<_>(&location, x2, x1)) x1)
            end
            do ()

    let parseAndStoreDocument env (document: _ byref) triviaStart triviaLength =
        modifyByCas &document (function
            | Some _ as r -> r
            | _ ->

            match triviaLength with
            | 0 -> Some struct([], [])
            | l ->

            let source = env.rare.noUpdate.source.Value
            Pool.using Scanner.pool <| fun s ->
            Scanner.init source s
            Parser.DocumentParser.documents s triviaStart l |> Some
        )
        Option.get document

    let parseAndStoreLeadingDocument env t =
        let l = t.leadingTriviaLength
        parseAndStoreDocument env &t.leadingDocument (t.span.start - l) l

    let parseAndStoreTrailingDocument env t =
        let l = t.trailingTriviaLength
        parseAndStoreDocument env &t.trailingDocument t.span.end' l

    let leadingDocuments env t =
        match t.leadingDocument with
        | Some x -> x
        | _ -> parseAndStoreLeadingDocument env t

    let leadingDocumentSpan t =
        let tokenStart = t.span.start
        { start = tokenStart - t.leadingTriviaLength; end' = tokenStart }

    let trailingDocuments env t =
        match t.trailingDocument with
        | Some x -> x
        | _ -> parseAndStoreTrailingDocument env t

    let trailingDocumentSpan t =
        let tokenEnd = t.span.end'
        { start = tokenEnd; end' = tokenEnd + t.trailingTriviaLength }

    let checkLeadingGlobalTags env syntaxShape syntax =
        match Syntax.firstTrivia syntaxShape syntax with
        | ValueSome t -> DocumentCheckers.statementLevelTags env (leadingDocumentSpan t) (leadingDocuments env t)
        | _ -> ()

    let checkTrailingGlobalTags env syntaxShape syntax =
        match Syntax.lastTrivia syntaxShape syntax with
        | ValueSome t -> DocumentCheckers.statementLevelTags env (trailingDocumentSpan t) (trailingDocuments env t)
        | _ -> ()

    let trySetSchemeInstantiationInfo scheme tvs instantiated = function
        | { kind = T.Variable(T.Var(k, s, r, n, t, info)) } as e ->
            let info =
                match info with
                | ValueNone -> T.LeafInfo.empty
                | ValueSome info -> info

            let info =
                ValueSome { info with T.schemeInstantiation = ValueSome(scheme, tvs) }

            struct({ e with kind = T.Variable(T.Var(k, s, r, n, t, info)) }, instantiated)

        | e -> struct(e, instantiated)

    let instantiate env struct(e, scheme) =
        let struct(tvs, instantiated) = Scheme.instantiate env.rare.typeLevel scheme
        match tvs with
        | _::_ -> trySetSchemeInstantiationInfo scheme tvs instantiated e
        | _ -> struct(e, instantiated)

    let unifyDecl env d1 d2 =
        if d1.declarationFeatures <> d2.declarationFeatures then
            true
        else
            match unify env d1.scheme d2.scheme with
            | ValueSome _ -> true
            | _ -> false

    let mergeNames env (NonEmptyList(d, ds) as dds) (NonEmptyList(d', ds') as dds') =
        match ds, ds', unifyDecl env d d' with
        | [], [], false -> dds
        | _, _, false -> NonEmptyList(d, ds @ ds')
        | _, _, true -> NonEmptyList.append dds dds'

    let extendGlobalEnvironmentFromParentModule env span modulePath { T.additionalGlobalEnv = parentEnv } =

        // 親モジュールのグローバル環境を現在の環境に導入する
        env.rare.noUpdate.additionalGlobalEnv
        |> Local.modify (fun childEnv ->
            Env.merge
                (mergeNames env)

                // TODO: 型定義が互換性を持つなら統合する
                NonEmptyList.append

                childEnv
                parentEnv
        )

        // チャンクトップレベル = エラーが無ければ必ず実行される
        if not <| Map.isEmpty parentEnv.names && not env.rare.isChunkTop then

            // グローバル環境が不確定になってしまうので警告
            // 例えば `if x then require 'lib1' else end` のような場合
            // `x` の値によってグローバル変数が定義されるかが決まる
            reportWarn env span <| DiagnosticKind.UndeterminedGlobalVariableEnvironment(modulePath, parentEnv.names)

    let reportMostSeriousErrorOnModuleRequire env span modulePath e =
        match mostSeriousDiagnostic e with
        | ValueSome(Diagnostic(_, s, _) as e) ->
            report env <| Diagnostic(span, s, DiagnosticKind.ExternalModuleError(modulePath, e))
        | _ -> ()

    let missingChunk (Types types as env) syntaxSpan functionTypeLocations = {
        kind = {
            T.semanticTree = {
                kind = { T.stats = []; T.lastStat = None }
                trivia = syntaxSpan
            }
            T.functionType =
                types.fn(
                    newMultiVarType env TypeNames.lostByError |@ functionTypeLocations,
                    newMultiVarType env TypeNames.lostByError |@ functionTypeLocations
                ) |@ functionTypeLocations
                |> Scheme.generalize env.rare.typeLevel

            T.ancestorModulePaths = Set.empty
            T.additionalGlobalEnv = Env.empty
        }
        trivia = syntaxSpan
    }

    let analyzeModuleFile env span modulePath moduleFile =
        match moduleFile.stage with

        // モジュールが解析完了していたのでそれを使う
        | AnalysisComplete(s, e) ->
            reportMostSeriousErrorOnModuleRequire env span modulePath e
            s.typedTree

        // モジュールは未解析だった
        | _ ->

        let visitedSources = env.rare.noUpdate.visitedSources

        if Set.contains modulePath visitedSources.Value then
            // 解析中のモジュールを再び解析しようとしている ( = モジュール参照が再帰していた ) のでエラー
            // TODO: モジュールがテーブル型なら再帰できる
            reportWarn env span <| DiagnosticKind.RecursiveModuleReference modulePath
            missingChunk env span []
        else

        // 再帰モジュール参照ではなかった
        let projectRef = env.rare.noUpdate.project
        let tree, e, project = checkSourceFileCached' visitedSources projectRef.Value modulePath moduleFile
        projectRef.Value <- project
        reportMostSeriousErrorOnModuleRequire env span modulePath e
        tree

    let appendAncestorModulePaths env modulePaths =
        let ancestors = env.rare.noUpdate.ancestorModulePaths
        ancestors.Value <- ancestors.Value + modulePaths

let literalType (Types types) x location = types.literal(x, location)

let binaryExpType (Types types & TypeCache typeCache as env) (e1, t1) op (e2, t2) =
    let l = sourceLocation env op.trivia.span
    match op.kind with

    // type(a) -> fun(a, a) -> a
    | Or
    | And ->
        let a = newValueVarType env "a" |@ l
        unifyDiagnosticsAt env e1 a t1
        unifyDiagnosticsAt env e2 a t2

        let t = types.fn(multiType2 env l a a, multiType1 env a l) |@ l
        struct {| result = a; operator = t |}

    // type(a: ..(number | string), b: boolean..) -> fun(a, a) -> b
    | Lt
    | Gt
    | Le
    | Ge ->
        let a = newValueVarTypeWith env "a" (typeCache.numberOrStringOrLowerConstraint |@ l) |@ l
        unifyDiagnosticsAt env e2 t1 a
        unifyDiagnosticsAt env e2 t2 a

        let r = newValueVarTypeWith env "b" (typeCache.booleanOrUpperConstraint |@ l) |@ l
        let t = types.fn(multiType2 env l a a, multiType1 env r l) |@ l
        {| result = r; operator = t |}

    // type(a, b: boolean..) -> fun(a, a) -> b
    | Eq
    | Ne ->
        let a = newValueVarType env "a" |@ l
        unifyDiagnosticsAt env e1 t1 a
        unifyDiagnosticsAt env e2 t2 a

        let r = newValueVarTypeWith env "b" (typeCache.booleanOrUpperConstraint |@ l) |@ l
        let t = types.fn(multiType2 env l a a, multiType1 env r l) |@ l
        {| result = r; operator = t |}

    // type(a: ..string, b: ..string, c: string..) -> fun(a, b) -> c
    | Con ->
        let c = typeCache.stringOrLowerConstraint |@ l
        let a = newValueVarTypeWith env "a" c |@ l
        let b = newValueVarTypeWith env "b" c |@ l
        unifyDiagnosticsAt env e1 t1 a
        unifyDiagnosticsAt env e2 t2 b

        let r = newValueVarTypeWith env "c" (typeCache.stringOrUpperConstraint |@ l) |@ l
        let t = types.fn(multiType2 env l t1 t2, multiType1 env r l) |@ l
        {| result = r; operator = t |}

    // type(a: ..number, b: ..number, c: number..) -> fun(a, b) -> c
    | Add
    | Sub
    | Mul
    | Div
    | Mod
    | Pow ->
        let c = typeCache.numberOrLowerConstraint |@ l
        let a = newValueVarTypeWith env "a" c |@ l
        let b = newValueVarTypeWith env "b" c |@ l
        unifyDiagnosticsAt env e1 t1 a
        unifyDiagnosticsAt env e2 t2 b
        let r = newValueVarTypeWith env "c" (typeCache.numberOrUpperConstraint |@ l) |@ l
        let t = types.fn(multiType2 env l a b, multiType1 env r l) |@ l
        {| result = r; operator = t |}

let unaryExpType (Types types & TypeCache typeCache as env) op (e1, t1) =
    let l = sourceLocation env op.trivia.span
    match op.kind with
    // type(a: ..(string | table), b: number..) -> fun(a) -> b
    | Len ->
        let a = newValueVarTypeWith env "a" (typeCache.stringOrTableOrLowerConstraint |@ l) |@ l
        let r = newValueVarTypeWith env "b" (typeCache.numberOrUpperConstraint |@ l) |@ l
        unifyDiagnosticsAt env e1 t1 a
        let t = types.fn(multiType1 env a l, multiType1 env r l) |@ l
        struct {| result = r; operator = t |}

    // type(a: ..number, b: number..) -> fun(a) -> b
    | Neg ->
        let a = newValueVarTypeWith env "a" (typeCache.numberOrLowerConstraint |@ l) |@ l
        unifyDiagnosticsAt env e1 t1 a
        let r = newValueVarTypeWith env "b" (typeCache.numberOrUpperConstraint |@ l) |@ l
        let t = types.fn(multiType1 env a l, multiType1 env r l) |@ l
        {| result = r; operator = t |}

    // type(a, b: boolean..) -> fun(a) -> b
    | Not ->
        let r = newValueVarTypeWith env "b" (typeCache.booleanOrUpperConstraint |@ l) |@ l
        let t = types.fn(multiType1 env t1 l, multiType1 env r l) |@ l
        {| result = r; operator = t |}

let varArgExp env varArg =
    let t = multiTypeAsSingleType env (Token.measure varArg) env.rare.varArgType
    let var = T.ReservedVar(varArg.trivia, TokenKind.Dot3, t, ValueNone)
    struct(withSpan varArg.trivia.span <| T.VarArg var, t)

let exp env x =
    match x.kind with

    | VarArg v -> varArgExp env v

    | Literal({ kind = k } as l) ->
        literal x.trivia (literalType env k <| sourceLocation env l.trivia.span) l

    | Function(functionKeyword, body) ->
        let struct(body, functionType) = funcBody (enterTypeScope env) functionKeyword None [] body
        let functionType = Scheme.generalizeAndAssign env.rare.typeLevel functionType
        withSpan x.trivia <| T.Function body, functionType

    | PrefixExp x -> prefixExp env x
    | NewTable x -> tableConstructor env x
    | Binary(e1, { kind = k } & op, e2) ->
        let struct(x1, t1) = exp env e1
        let struct(x2, t2) = exp env e2
        let t = binaryExpType env (e1, t1) op (e2, t2)
        let op = T.ReservedVar(op.trivia, TokenKind.ofBinaryOpKind k, t.operator, ValueNone)
        withSpan x.trivia <| T.Binary(x1, op, x2), t.result

    | Unary({ kind = k } as op, e1) ->
        let struct(x1, t1) = exp env e1
        let t = unaryExpType env op (e1, t1)
        let op = T.ReservedVar(op.trivia, TokenKind.ofUnaryOpKind k, t.operator, ValueNone)
        withSpan x.trivia <| T.Unary(op, x1), t.result

[<RequireQualifiedAccess>]
type RestTyping =
    /// `?e...(?x: nil..)`
    | NilOrUppers
    /// `()`
    | Empty

let multiExp env rest x =
    match x.kind with

    // 複型
    // `…, f()`
    | PrefixExp { kind = Apply x } ->
        let struct(call, resultType) = functionCall env x
        struct(call, resultType)

    // 複型
    // `…, ...`
    | VarArg dot3 ->
        let t = env.rare.varArgType
        let var = T.ReservedVar(dot3.trivia, TokenKind.Dot3, t, ValueNone)
        let var = withSpan dot3.trivia.span <| T.VarArg var
        var, t

    // 1つの値を持つ複型
    // `…, (f())`
    | _ ->
        let struct(x', xt) = exp env x
        let t =
            let l = sourceLocation env x.trivia
            match rest with
            | RestTyping.NilOrUppers -> multiType1AndNilOrUppers env xt l
            | RestTyping.Empty -> multiType1 env xt l
        x', t

let expList env rest = function
    | NonEmptyList(head, []) ->
        let struct(head, t) = multiExp env rest head
        struct(NonEmptyList.singleton head, t)

    | NonEmptyList(head, x::xs) ->
        let struct(head, headType) = exp env head
        let struct(xs, t) = expList env rest (NonEmptyList(x, xs))
        NonEmptyList.cons head xs, (types env).cons(headType, t) |@ sourceLocation env x.trivia

let memberType env selfType (Name({ kind = n } as name)) =
    let nameLocation = sourceLocation env name.trivia.span
    let valueType = newValueVarType env n |@ nameLocation
    let key = FieldKey.String n
    let selfConstraint = Map.add key valueType Map.empty |> Constraints.ofInterfaceType |@ nameLocation
    let t = newValueVarTypeWith env TypeNames.indexSelf selfConstraint |@ nameLocation
    reportIfUnifyError env name.trivia.span selfType t
    valueType

let variableDecl env (Name { kind = name } as n) =
    let nameSpan = Name.measure n
    match resolveVariable nameSpan name env with
    | ValueSome({ declarationFeatures = k } as d) ->
        match k with
        | DeclarationFeatures.NoFeatures -> ()
        | DeclarationFeatures.GlobalRequire ->
            reportInfo env nameSpan <| DiagnosticKind.IndirectGlobalRequireUse
        | DeclarationFeatures.GlobalPackage ->
            reportInfo env nameSpan DiagnosticKind.UnrecognizableGlobalPackageUse

        d

    | _ ->
        reportError env (Name.measure n) <| DiagnosticKind.NameNotFound name
        {
            scheme = newValueVarType env TypeNames.lostByError |@ sourceLocation env nameSpan
            declarationFeatures = DeclarationFeatures.NoFeatures
            declarationScope = S.Local
            declarationKind = I.Variable
            declarationRepresentation = IdentifierRepresentation.Definition
            location = None
        }

let variable env span name =
    let { scheme = t } as d = variableDecl env name
    struct(withSpan span <| T.Variable(makeVar d.declarationScope d.declarationKind R.Reference name t), t)

let var env x =
    match x.kind with
    | Variable n -> variable env x.trivia n
    | Index(self, _, key, _) ->
        let struct(self', selfType) = prefixExp env self
        let struct(key', keyType) = exp env key
        let staticKey = staticKey key
        let valueName =
            match staticKey with
            | ValueSome k -> TypeNames.fromFieldKey k
            | _ -> ValueNone

        let valueName = ValueOption.defaultValue TypeNames.fieldValue valueName
        let valueType = newValueVarType env valueName |@ sourceLocation env x.trivia

        match staticKey with
        | ValueSome k ->

            // 静的なキーならインターフェース制約のついた型変数
            // `t[true]` => `t: ('t: { true: ?v })`
            // `t[0]` => `t: ('t: { 0: ?v })`
            let l = sourceLocation env key.trivia
            let selfConstraint = Map.add k valueType Map.empty |> Constraints.ofInterfaceType |@ l
            let c = newValueVarTypeWith env TypeNames.indexSelf selfConstraint |@ l
            unifyDiagnosticsAt env key selfType c

        | _ ->

            // 動的なキーならテーブル型
            // `t[k]` => `k: ?k` `t: table<?k,?v>`
            unifyDiagnosticsAt env key selfType (types(env).table(keyType, valueType) |@ sourceLocation env x.trivia)

        withSpan x.trivia <| T.Index(self', key'), valueType

    | Member(self, _, name) ->
        let struct(self, selfType) = prefixExp env self
        let resultType = memberType env selfType name
        let name = makeVar S.Member I.Field R.Reference name resultType
        withSpan x.trivia <| T.Member(self, name), resultType

let prefixExp env x =
    match x.kind with
    | Apply x ->
        let struct(call, resultType) = functionCall env x
        let resultType = multiTypeAsSingleType env x.trivia resultType
        struct(call, resultType)

    | Var x -> var env x
    | Wrap(l, x, r) -> wrap env (l, x, r)

let wrap env (l, x, _) =
    let struct(x', t) = exp env x
    match DocumentCheckers.findTypeTag env (leadingDocumentSpan l.trivia) (leadingDocuments env l.trivia) with
    | ValueNone -> x', t
    | ValueSome(typeSign, t') -> withSpan x.trivia <| T.TypeReinterpret(typeSign, x', t'), t'

let isExplicitStaticKey = function
    | Init _
    | MemberInit(Name _, _, _)
    | IndexInit(_, { kind = Literal _ }, _, _, _) -> true
    | _ -> false

[<Struct>]
type TableCheckState = {
    hasExplicitKey: bool
    hasDynamicKey: bool
    itemIndex: int
}
type FieldCheckResult = {
    field: Field
    keyType: Type
    keyExp: Exp voption
    valueType: Type
    valueExp: Exp
    resultExp: T.Field
    key: FieldKey voption
}
let field env ({ itemIndex = itemIndex } as state) f =
    match f.kind with
    | Init v ->
        let struct(v', vt) = exp env v
        let k = double itemIndex
        let info = {
            field = f
            keyType = literalType env (Number k) <| sourceLocation env v.trivia
            keyExp = ValueNone
            valueType = vt
            valueExp = v
            resultExp = withSpan f.trivia <| T.Init v'
            key = ValueSome <| FieldKey.Number k
        }
        let state = { state with itemIndex = itemIndex + 1 }
        struct(info, state)

    | MemberInit(Name { kind = k } as key, _, v) ->
        let struct(v', vt) = exp env v
        let k' = makeVar S.Member I.Field R.Definition key vt
        let info = {
            field = f
            keyType = literalType env (String k) <| sourceLocation env (Name.measure key)
            keyExp = ValueNone
            valueType = vt
            valueExp = v
            resultExp = withSpan f.trivia <| T.MemberInit(k', v')
            key = ValueSome <| FieldKey.String k
        }
        let state = { state with hasExplicitKey = true }
        info, state

    | IndexInit(_, k, _, _, v) ->
        let struct(k', kt) = exp env k
        let struct(v', vt) = exp env v
        let info = {
            field = f
            keyType = kt
            keyExp = ValueSome k
            valueType = vt
            valueExp = v
            resultExp = withSpan f.trivia <| T.IndexInit(k', v')
            key = ValueNone
        }
        let state = {
            state with
                hasExplicitKey = true
                hasDynamicKey = state.hasDynamicKey || not (isStaticKey k)
        }
        info, state

let nameListNoExtend env lastMultiType names =
    let nameAndTypes =
        names
        |> NonEmptyList.map (fun (Name { kind = name } as n) ->
            let t = newValueVarType env name |@ sourceLocation env (Name.measure n)
            struct(n, t)
        )
    let namesType =
        NonEmptyList.foldBack (fun struct(n, t) lastM ->
            (types env).cons(t, lastM) |@ sourceLocation env (Name.measure n)
        ) nameAndTypes lastMultiType

    struct(nameAndTypes, namesType)

let nameList env idKind idScope idRepr lastMultiType names =
    let struct(nameAndTypes, namesType) = nameListNoExtend env lastMultiType names
    let struct(names, env) =
        nameAndTypes
        |> NonEmptyList.mapFold (fun env struct(Name n as name, t) ->
            let location = Some <| Location(env.rare.noUpdate.filePath, n.trivia.span)
            let name = makeVar idKind idScope idRepr name t
            let env = extend location idKind idScope idRepr n.kind (Scheme.ofType t) env
            name, env
        ) env
    struct(names, namesType, env)

let varArgParameter env dot3 =
    let l = sourceLocation env dot3.trivia.span
    let varArgType = newMultiVarType env TypeNames.implicitMultiVar |@ l
    let varArg =
        T.ReservedVar(
            dot3.trivia,
            TokenKind.Dot3,
            varArgType,
            ValueNone
        )
    struct(varArg, varArgType)

let funcBody (Types types as env) functionKeyword name implicitParameters { kind = FuncBody(lb, parameters, rb, body, end'); trivia = t } =
    let names, dot3, parameterListSpan =
        match parameters with
        | None -> NonEmptyList.tryOfList implicitParameters, None, Span.merge lb.trivia.span rb.trivia.span
        | Some ps ->

        match ps.kind with
        | VarParameter varArg -> NonEmptyList.tryOfList implicitParameters, Some varArg, ps.trivia
        | ParameterList(names, varArg) ->

        let varArg = match varArg with Some(_, varArg) -> Some varArg | _ -> None
        ValueSome <| NonEmptyList.appendList implicitParameters (SepBy.toNonEmptyList names.kind), varArg, ps.trivia

    let struct(varArg, varArgType) =
        match dot3 with
        | None -> None, types.empty |@ sourceLocation env parameterListSpan
        | Some dot3 ->
            let struct(varArg, varArgType) = varArgParameter env dot3
            Some varArg, varArgType

    let struct(parameters, parameterAndVarArgType, env') =
        match names with
        | ValueSome names ->
            let struct(names, parameterAndVarArgType, env) = nameList env S.Local I.Parameter R.Definition varArgType names
            let parameters = T.ParameterList(NonEmptyList.toList names, varArg) |> withSpan parameterListSpan |> Some
            parameters, parameterAndVarArgType, env
        | _ ->
            None, varArgType, env

    let returnType = newMultiVarType env TypeNames.functionResult |@ sourceLocation env t
    let location =
        match name with
        | Some(location, _, _, _) -> Option.toList location
        | _ -> sourceLocation env functionKeyword.trivia.span

    let functionType = types.fn(parameterAndVarArgType, returnType) |@ location
    let env' =
        match name with
        | Some(location, scope, repr, name) -> extend location scope I.Variable repr name (Scheme.ofType functionType) env'
        | _ -> env'

    let env' = enterChunkLocal env'
    let env' = enterTemporaryTypeVarNameScope env'
    let env' = {
        env' with
            rare = {
                env'.rare with
                    returnType = returnType
                    varArgType = varArgType
            }
    }
    let state = { isImplicitReturn = true }
    let struct(block, _, state) = block env' state body
    if state.isImplicitReturn then
        reportIfUnifyError env' (Token.measure end') env'.rare.returnType (nilOrUppers env <| sourceLocation env end'.trivia.span)

    let x = withSpan t <| T.FuncBody(parameters, block)
    struct(x, functionType)

let tableConstructorType (Types types as env) tableSpan state fields =
    let tableLocation = sourceLocation env tableSpan

    // 全てのフィールドにキーが指定されていないなら配列
    // `{ item1, item2, … }` => table<integer,?a> = array<?a>
    if not state.hasExplicitKey && not state.hasDynamicKey then

        // 全ての配列の値の型が同じかチェック
        let valueType = newValueVarType env TypeNames.arrayValue |@ tableLocation
        for f in fields do
            unifyDiagnosticsAt env f.valueExp f.valueType valueType

        types.table(types.number |@ tableLocation, valueType) |@ tableLocation

    // 全てのフィールドに静的なキーが指定されているならインターフェース
    // `{ a = x, ["b"] = y, … }` => { a: ?x, b: ?y, … }
    elif not state.hasDynamicKey then
        fields
        |> List.fold (fun map -> function
            | { key = ValueSome key; valueType = vt } -> Map.add key vt map
            | _ -> map
        ) Map.empty
        |> InterfaceType
        |> Type.makeWithLocation tableLocation

    // 他の場合テーブル
    // `{ [a] = x, [b] = y }` => table<?k, ?a>
    else
        // 全てのキーの型と値の型が同じかチェック
        let keyType = newValueVarType env TypeNames.arrayKey |@ tableLocation
        let valueType = newValueVarType env TypeNames.arrayValue |@ tableLocation
        for f in fields do
            match f.keyExp with
            | ValueSome k -> unifyDiagnosticsAt env k f.keyType keyType
            | _ -> unifyDiagnosticsAt env f.field f.keyType keyType
            unifyDiagnosticsAt env f.valueExp f.valueType valueType
        types.table(keyType, valueType) |@ tableLocation

let lastField env state f =
    match f.kind with

    // `{…, f()}`
    | Init v ->
        let struct(v', valuesType) = multiExp env RestTyping.Empty v
        let fieldLocation = sourceLocation env f.trivia
        let elementType = newValueVarType env TypeNames.multiElement |@ fieldLocation
        let c = MultiElementTypeConstraint elementType |@ fieldLocation
        let expectedType = newMultiVarTypeWith env TypeNames.multiElements c |@ fieldLocation

        // unify number (?expectedType...: ?elementType) => [?elementType := number]
        reportIfUnifyError env f.trivia valuesType expectedType

        let info = {
            field = f
            keyType = types(env).number |@ fieldLocation
            keyExp = ValueNone
            valueType = elementType
            valueExp = v
            resultExp = withSpan f.trivia <| T.Init v'
            key = ValueNone
        }
        let state =
            { state with
                itemIndex = state.itemIndex + 1
                hasDynamicKey = true
            }
        struct(info, state)

    | _ -> field env state f

let fieldList env state acc = function
    | NonEmptyList(f, []) ->
        let struct(f, state) = lastField env state f
        List.rev (f::acc), state

    | NonEmptyList(f1, f2::fs) ->
        let struct(f1, state) = field env state f1
        fieldList env state (f1::acc) (NonEmptyList(f2, fs))

let tableConstructor (Types types as env) { kind = TableConstructor(_, fs, _); trivia = tableSpan } =
    let tableLocation = sourceLocation env tableSpan
    match fs with

    // 空のテーブルはテーブル
    // `{}` => table<?k,?v>
    | None ->
        let t =
            types.table(
                newValueVarType env TypeNames.arrayKey |@ tableLocation,
                newValueVarType env TypeNames.arrayValue |@ tableLocation
            ) |@ tableLocation
        withSpan tableSpan <| T.NewTable [], t

    | Some(FieldList(fs, _)) ->
        let state = {
            hasExplicitKey = false
            hasDynamicKey = false
            itemIndex = 1
        }
        let fields, state = fieldList env state [] <| SepBy.toNonEmptyList fs
        let tableType = tableConstructorType env tableSpan state fields

        let fields = fields |> List.map (fun f -> f.resultExp)
        withSpan tableSpan <| T.NewTable fields, tableType

let args (Types types as env) x =
    match x.kind with
    | StringArg(StringLiteral s) ->
        let location = sourceLocation env s.trivia.span
        let t =
            let c = Constraints.literal1 (String s.kind) |@ location
            newValueVarTypeWith env s.kind c |@ location

        let l = { kind = String s.kind; trivia = s.trivia }
        let struct(literal, literalType) = literal x.trivia t l
        struct([literal], multiType1 env literalType location)

    | TableArg x ->
        let struct(x', xt) = tableConstructor env x
        [x'], multiType1 env xt <| sourceLocation env x.trivia

    | Args(_, None, _) -> [], types.empty |@ sourceLocation env x.trivia
    | Args(_, Some { kind = vs }, _) ->
        let struct(xs, t) = SepBy.toNonEmptyList vs |> expList env RestTyping.Empty
        NonEmptyList.toList xs, t

let processRequireCall env callSpan (moduleName, nameSpan) =
    let callLocation = sourceLocation env callSpan

    match resolveModuleFile env moduleName with

    // モジュールは見つからなかった
    | Error moduleFiles ->

        // エラーを報告
        reportWarn env nameSpan <| DiagnosticKind.ModuleNotFound(moduleName, moduleFiles)

        // モジュール候補のパスを自分の先祖として追加
        appendAncestorModulePaths env <| Set.ofList moduleFiles

        None, newMultiVarType env TypeNames.lostByError |@ callLocation

    // モジュールのパスが解決できた
    | Ok(modulePath, moduleFile) ->

    // モジュールを解析してエラー報告
    let { kind = chunk } = analyzeModuleFile env nameSpan modulePath moduleFile

    // モジュールのパスとモジュールの先祖のパスを自分の先祖に追加
    appendAncestorModulePaths env <| Set.add modulePath chunk.ancestorModulePaths

    // 戻り値型を求める
    let resultType =
        let struct(_, t) = Scheme.instantiate env.rare.typeLevel chunk.functionType
        let typeEnv = typeEnv env
        match t.kind with
        | Type.Function typeEnv (ValueSome(_, r)) -> r
        | _ -> t

    // モジュールの追加的グローバル環境を導入する
    extendGlobalEnvironmentFromParentModule env nameSpan modulePath chunk

    Some modulePath, resultType

let functionCall (Types types as env) x =
    match x.kind with

    // `require("…")`
    | RequireCall env c ->
        let Name fn as f = c.requireName
        let nameLocation = sourceLocation env c.moduleNameTrivia.span
        let modulePath, resultType = processRequireCall env x.trivia (c.moduleName, c.moduleNameTrivia.span)
        let functionType =
            types.fn(
                multiType1 env (types.string |@ nameLocation) nameLocation,
                resultType
            )
            |@ sourceLocation env fn.trivia.span

        let require' = makeVar S.Global I.Variable R.Reference f functionType
        let require' = withSpan fn.trivia.span <| T.Variable require'
        let trivia =
            modulePath
            |> Option.unbox
            |> ValueOption.map (fun modulePath ->
                { T.LeafInfo.empty with T.externalModulePath = ValueSome modulePath }
            )

        let moduleName' = { kind = String c.moduleName; trivia = c.moduleNameTrivia }
        let moduleName' = T.Literal(moduleName', types.string |@ nameLocation, trivia)
        let moduleName' = withSpan c.moduleNameTrivia.span moduleName'
        withSpan x.trivia <| T.Call(require', [moduleName']), resultType

    // `f vs`
    // f: (fun('vs): 'result)
    // vs: 'vs
    | Call(f, vs) ->
        let struct(f', ft) = prefixExp env f
        let struct(f', ft) = instantiate env (f', ft)
        let struct(args', argTypes) = args env vs
        let calleeLocation = sourceLocation env f.trivia
        let resultType = newMultiVarType env TypeNames.functionResult |@ calleeLocation
        unifyDiagnosticsAt env vs ft (types.fn(argTypes, resultType) |@ calleeLocation)
        withSpan x.trivia <| T.Call(f', args'), resultType

    // `self:name vs`
    // self: ('self: { name: fun('self, 'vs...): 'result })
    // vs: 'vs...
    | CallWithSelf(self, _, (Name { kind = name } as n), vs) ->
        let struct(self, selfType) = instantiate env (prefixExp env self)
        let struct(args, argTypes) = args env vs
        let nameLocation = sourceLocation env (Name.measure n)
        let resultType = newMultiVarType env TypeNames.functionResult |@ nameLocation
        let functionType = types.fn(types.cons(selfType, argTypes) |@ nameLocation, resultType) |@ nameLocation
        let selfConstraint = Constraints.ofInterfaceType <| Map.add (FieldKey.String name) functionType Map.empty |@ nameLocation
        unifyDiagnosticsAt env vs selfType (newValueVarTypeWith env TypeNames.indexSelf selfConstraint |@ nameLocation)
        let name = makeVar S.Member I.Method R.Reference n functionType
        withSpan x.trivia <| T.CallWithSelf(self, name, args), resultType

let stat env state x =
    checkLeadingGlobalTags env Syntax.stat x

    let span = x.trivia
    let struct(s, env, state) =
        match x.kind with
        | Local(_, names, values) -> local env state span (names, values)
        | Assign(vars, _, values) -> assign env state span (vars, values)
        | FunctionCall call -> functionCallStat env state span call
        | Do(_, body, _) -> doStat env state span body
        | While(_, cond, _, body, _) -> whileStat env state span (cond, body)
        | RepeatUntil(_, body, _, cond) -> repeatUntil env state span (body, cond)
        | If(_, cond, _, ifTrue, elseIfClauses, elseClause, _) -> ifStat env state span (cond, ifTrue, elseIfClauses, elseClause)
        | For(_, var, _, start, _, stop, step, _, body, _) -> forStat env state span (var, start, stop, step, body)
        | ForIn(_, names, _, exprs, _, body, _) -> forIn env state span (names, exprs, body)
        | FunctionDecl(keyword, name, body) -> functionDecl env state span (keyword, name, body)
        | LocalFunction(_, functionKeyword, var, body) -> localFunction env state span (functionKeyword, var, body)

    checkTrailingGlobalTags env Syntax.stat x
    struct(s, env, state)

// `local name,… = value,…`
let local env state span (names, values) =
    let struct(values, valuesType) =
        match values with
        | None -> [], types(env).empty |@ sourceLocation env span
        | Some(_, { kind = es }) ->
            let env = enterTypeScope env
            let struct(es, t) = expList env RestTyping.NilOrUppers <| SepBy.toNonEmptyList es
            NonEmptyList.toList es, t

    let namesOverflow = newMultiVarType (enterTypeScope env) TypeNames.multiOverflow |@ sourceLocation env span
    let struct(nameAndTypes, namesType) = nameListNoExtend (enterTypeScope env) namesOverflow (SepBy.toNonEmptyList names.kind)

    // 両辺の型を単一化
    reportIfUnifyError env names.trivia namesType valuesType
    // namesType = ( ?x1(1) := (?n(1): (1 | 2)..) ,)
    // nameAndTypes = [ `x1`, (?x1(1) := (?n(1): (1 | 2)..)) ]

    // 変数の型を汎用化
    let nameAndTypes2 =
        nameAndTypes
        |> NonEmptyList.map (fun struct(n, t) ->
            let t = Scheme.generalizeAndAssign env.rare.typeLevel t
            struct(n, t)
        )

    // 変数の名前と型を環境に登録
    let env =
        nameAndTypes2
        |> NonEmptyList.fold (fun env struct(Name n, t) ->
            let location = Some <| Location(env.rare.noUpdate.filePath, n.trivia.span)
            extend location S.Local I.Variable R.Definition n.kind t env
        ) env

    let names' =
        nameAndTypes2
        |> NonEmptyList.map (fun struct(n, t) -> makeVar S.Local I.Variable R.Definition n t)

    let stat = T.Local(names', values) |> withSpan span
    struct(stat, env, state)

// var,… = value,…
let assign' (Types types as env) state span ({ kind = vars } as vs, { kind = values; trivia = valuesSpan }) =
    let struct(values, valueType) = expList env RestTyping.NilOrUppers <| SepBy.toNonEmptyList values
    let vars = SepBy.toNonEmptyList vars |> NonEmptyList.map (var env)
    let varsOverflow = newMultiVarType env TypeNames.multiOverflow |@ sourceLocation env valuesSpan
    let varsType =
        NonEmptyList.foldBack (fun struct({ trivia = varSpan }, varType) lastType ->
            types.cons(varType, lastType) |@ sourceLocation env varSpan
        ) vars varsOverflow

    let vars = vars |> NonEmptyList.map (fun struct(v, _) -> v)
    reportIfUnifyError env vs.trivia varsType valueType
    let stat = T.Assign(vars, values) |> withSpan span
    struct(stat, env, state)

let updatePackagePathStat env state span (vars, values) (left, right) =
    let env = modifyPackagePath env <| fun path -> Option.defaultValue "" left + path + Option.defaultValue "" right
    let struct(oldSuppressState, env) = suppressDiagnostics true env
    let struct(assign, env, state) = assign' env state span (vars, values)
    let struct(_, env) = suppressDiagnostics oldSuppressState env
    struct(assign, env, state)

let assign env state span (vars, values) =
    match struct(vars.kind, values.kind) with
    | StaticUpdatePackagePath env (left, right) -> updatePackagePathStat env state span (vars, values) (left, right)
    | _ -> assign' env state span (vars, values)

let functionCallStat env state span call =
    let struct(call', callType) = functionCall env call
    match unify env callType (types(env).empty |@ sourceLocation env span) with
    | ValueSome _ -> reportInfo env call.trivia DiagnosticKind.ReturnValueIgnored
    | _ -> ()

    let stat = T.FunctionCall call' |> withSpan span
    stat, env, state

let doStat env state span body =
    let struct(body, _, state) = block env state body
    withSpan span <| T.Do body, env, state

let whileStat env state span (cond, body) =
    let env' = enterChunkLocal env
    let struct(cond', condType) = exp env' cond
    let l = sourceLocation env cond.trivia
    let c = typeCache(env').booleanOrLowerConstraint |@ l
    let v = newValueVarTypeWith env TypeNames.condition c |@ l
    unifyDiagnosticsAt env' cond condType v
    let struct(body', _, state') = block env' state body
    let state =
        if isInfinityLoop cond body then { state with isImplicitReturn = false }
        else StatState.merge state state'

    withSpan span <| T.While(cond', body'), env, state

let repeatUntil env state span (body, cond) =
    let struct(body', env', state') = block env state body
    let struct(cond', condType) = exp env' cond
    let l = sourceLocation env cond.trivia
    let c = typeCache(env').booleanOrLowerConstraint |@ l
    let v = newValueVarTypeWith env TypeNames.condition c |@ l
    unifyDiagnosticsAt env cond condType v
    let state =
        if isInfinityLoop cond body then state'
        else StatState.merge state state'

    let stat = withSpan span <| T.RepeatUntil(body', cond')
    stat, env, state

let ifStat env state span (cond, ifTrue, elseIfClauses, elseClause) =
    let env' = enterChunkLocal env
    let struct(cond', condType) = exp env' cond
    let l = sourceLocation env cond.trivia
    let c = typeCache(env').booleanOrLowerConstraint |@ l
    let v = newValueVarTypeWith env TypeNames.condition c |@ l
    unifyDiagnosticsAt env' cond condType v
    let struct(ifTrue, _, state') = block env' state ifTrue
    let mutable state' = state'

    let mutable elseIfs = []
    for { kind = ElseIf(_, cond, _, ifTrue) } in elseIfClauses do
        let struct(cond', condType) = exp env' cond
        let l = sourceLocation env cond.trivia
        let c = typeCache(env').booleanOrLowerConstraint |@ l
        let v = newValueVarTypeWith env TypeNames.condition c |@ l
        unifyDiagnosticsAt env' cond condType v
        let struct(ifTrue, _, state) = block env' state ifTrue
        state' <- StatState.merge state' state
        elseIfs <- T.ElseIf(cond', ifTrue)::elseIfs
    let elseIfs = List.rev elseIfs

    let else' =
        match elseClause with
        | None -> state' <- StatState.merge state' state; None
        | Some { kind = Else(_, ifFalse) } ->
            let struct(ifFalse, _, state) = block env' state ifFalse
            state' <- StatState.merge state' state
            Some ifFalse

    let stat = T.If(cond', ifTrue, elseIfs, else') |> withSpan span
    stat, env, state'

// for var: (?var: number..) = start: (?start: ..number), stop: (?stop: ..number), step: (?step: ..number) do … end
let forStat (TypeCache typeCache as env) state span (Name { kind = name; trivia = { span = nameSpan } } & var, start, stop, step, body) =
    let env' = enterChunkLocal env
    let varL = sourceLocation env nameSpan
    let struct(_, varV) = Scheme.instantiate env.rare.typeLevel (newValueVarTypeWith env TypeNames.forVar (typeCache.numberOrUpperConstraint |@ varL) |@ varL)
    let var = makeVar S.Local I.Variable R.Definition var varV
    let struct(start', startType) = exp env' start
    let startL = sourceLocation env start.trivia
    let startV = newValueVarTypeWith env TypeNames.forStart (typeCache.numberOrLowerConstraint |@ startL) |@ startL
    unifyDiagnosticsAt env' start startType startV
    let struct(stop', stopType) = exp env' stop
    let stopL = sourceLocation env stop.trivia
    let stopV = newValueVarTypeWith env TypeNames.forStop (typeCache.numberOrLowerConstraint |@ stopL) |@ stopL
    unifyDiagnosticsAt env' stop stopType stopV
    let step' =
        step |> Option.map (fun (_, step) ->
            let struct(step', stepType) = exp env' step
            let stepL = sourceLocation env step.trivia
            let stepV = newValueVarTypeWith env TypeNames.forStep (typeCache.numberOrLowerConstraint |@ stepL) |@ stepL
            unifyDiagnosticsAt env' step stepType stepV
            step'
        )

    let nameLocation = Some <| Location(env.rare.noUpdate.filePath, nameSpan)
    let env'' = extend nameLocation S.Local I.Variable R.Definition name (Scheme.ofType varV) env'
    let struct(body', _, state') = block env'' state body
    let state = StatState.merge state state'
    let stat = T.For(var, start', stop', step', body') |> withSpan span
    stat, env, state
(**
`for var_1, …, var_n in expList do block end` =
```
do
    local _f, _s, _var = expList
    while true do
    local var_1, … , var_n = _f(_s, _var)
    _var = var_1
    if _var == nil then break end
    block
    end
end
```
expList: ((('s, 'v) -> (('v | nil), 'vs...)), 's, 'v)
vars: ('v, 'vs...)
*)
let forIn (Types types as env) state span (names, exprs, body) =
    let env' = enterChunkLocal env
    let struct(exprs', exprsType) = expList env' RestTyping.Empty <| SepBy.toNonEmptyList exprs.kind

    let l = sourceLocation env exprs.trivia
    let s = newValueVarType env' TypeNames.forInState |@ l
    let v = newValueVarType env' TypeNames.forInFirstVar |@ l
    let vs = newMultiVarType env' TypeNames.forInRestVars |@ l
    // TODO: 'v | nil
    let f = types.fn(multiType2 env' l s v, types.cons(v, vs) |@ l) |@ l
    let iteratorType = types.cons(f, types.cons(s, types.cons(v, types.empty |@ l) |@ l) |@ l) |@ l
    reportIfUnifyError env' exprs.trivia exprsType iteratorType

    let varType = types.cons(v, vs) |@ l
    let struct(names', namesType, env'') = nameList env' S.Local I.Variable R.Definition (types.empty |@ l) (SepBy.toNonEmptyList names.kind)
    reportIfUnifyError env' names.trivia namesType varType

    let struct(body', _, state) = block env'' state body

    let stat = T.ForIn(names', exprs', body') |> withSpan span
    stat, env, state

let functionDecl env state span (functionKeyword, { kind = FuncName(var, path, methodName) }, body) =
    let { scheme = pathType } as pathDecl = variableDecl env var
    let var' = makeVar pathDecl.declarationScope I.Variable R.Reference var pathType

    let path', pathType =
        path
        |> List.mapFold (fun pathType (_, name) ->
            let pathType = memberType env pathType name
            makeVar S.Member I.Field R.Reference name pathType, pathType
        ) pathType

    let self', body' =
        match methodName with
        | None ->
            // `function a.f(vs…) return r end` =
            // `a.f = function(vs…) return r end`
            let struct(body', functionType) = funcBody env functionKeyword None [] body
            unifyDiagnosticsAt env body pathType functionType
            None, body'

        | Some(colon, methodName) ->
            // `function a.b:f(vs…) return r end` =
            // `a.b.f = function(self, vs…) return r end`

            // `vs…`: ?vs...
            // `r`: ?r
            // `a.b`: ('b: { f: (fun('b, ?vs...): ?r) })
            let pathType = memberType env pathType methodName
            let implicitSelf = Syntax.Name { kind = "self"; trivia = colon.trivia }
            let struct(body', functionType) = funcBody env functionKeyword None [implicitSelf] body
            reportIfUnifyError env (Name.measure methodName) pathType functionType

            let self = makeVar S.Member I.Method R.Reference methodName functionType
            Some self, body'

    let stat = T.FunctionDecl(var', path', self', body') |> withSpan span
    stat, env, state

let localFunction env state span (functionKeyword, Name { kind = name; trivia = nameTrivia } & var, body) =
    let env' = enterTypeScope env
    let nameLocation = Some <| Location(env.rare.noUpdate.filePath, nameTrivia.span)
    let struct(body, functionType) = funcBody env' functionKeyword (Some(nameLocation, S.Local, R.Definition, name)) [] body
    let functionScheme = Scheme.generalizeAndAssign env.rare.typeLevel functionType
    let env = extend nameLocation S.Local I.Variable R.Definition name functionScheme env
    let stat = T.LocalFunction(makeVar S.Local I.Variable R.Definition var functionScheme, body) |> withSpan span
    stat, env, state

let lastStat env state lastStatAndSemicolon =
    let x, _ = lastStatAndSemicolon
    checkLeadingGlobalTags env Syntax.lastStat lastStatAndSemicolon

    let struct(x', state) =
        match x.kind with
        | Break _ ->
            let stat = T.Break |> withSpan x.trivia
            struct(stat, state)

        | Return(returnK, es) ->
            let return', returnType =
                match es with
                | None -> [], nilOrUppers env <| sourceLocation env returnK.trivia.span
                | Some { kind = es } ->
                    let struct(es, t) = expList env RestTyping.NilOrUppers <| SepBy.toNonEmptyList es
                    NonEmptyList.toList es, t

            reportIfUnifyError env x.trivia env.rare.returnType returnType
            let stat = T.Return return' |> withSpan x.trivia
            stat, { state with isImplicitReturn = false }

    checkTrailingGlobalTags env Syntax.lastStat lastStatAndSemicolon
    struct(x', state)

let block env state { kind = x; trivia = s } =
    DocumentCheckers.statementLevelTags env (leadingDocumentSpan s) (leadingDocuments env s)

    let stats, struct(env, state) =
        x.stats
        |> List.mapFold (fun struct(env, state) (s, _) ->
            let struct(stat', env, state) = stat env state s
            stat', (env, state)
        ) (env, state)

    let lastStat, state =
        match x.lastStat with
        | None -> None, state
        | Some(s, q) ->
            let struct(s, state) = lastStat env state (s, q)
            Some s, state

    let block = withSpan s.span {
        T.stats = stats
        T.lastStat = lastStat
    }
    struct(block, env, state)

let chunkWithScope<'Scope,'RootScope> (scope: 'Scope Scope) (visitedSources: Local<'RootScope,_>) project env filePath source x =
    Local.modify (Set.add filePath) visitedSources

    let diagnostics = ResizeArray()
    let fs = project.projectRare.fileSystem
    let project = Local.create scope project
    let ancestorModulePaths = Local.create scope Set.empty

    let chunkTypeLevel = 1

    let additionalGlobalEnv = Local.create scope Env.empty
    let types = env.typeSystem
    let env = {
        nameToDeclaration = Map.empty
        rare = {
            nameToType = Map.empty
            typeLevel = chunkTypeLevel
            returnType = Type.newVar TypeNames.functionResult chunkTypeLevel types.multiKind |@ []
            varArgType = Type.newVar TypeNames.implicitMultiVar chunkTypeLevel types.multiKind |@ []

            temporaryTypeVarLevel = chunkTypeLevel
            temporaryTypeVarEnv = ref Map.empty

            isChunkTop = true
            selfType = ValueNone
            packagePath = env.packagePath
            suppressDiagnostics = false
            noUpdate = {
                types = types
                typeCache = env.derivedTypes
                diagnostics = diagnostics
                filePath = filePath
                source = lazy fetchSourceContents fs source
                project = project
                ancestorModulePaths = ancestorModulePaths
                visitedSources = visitedSources

                defaultGlobalEnv = env.initialGlobalEnv
                additionalGlobalEnv = additionalGlobalEnv
            }
        }
    }
    let state = {
        isImplicitReturn = true
    }
    let struct(body, env, state) = block env state x
    if state.isImplicitReturn then
        reportIfUnifyError env x.trivia.span env.rare.returnType (nilOrUppers env [])

    let chunkFunctionType = types.fn(env.rare.varArgType, env.rare.returnType) |@ []
    let functionScheme = Scheme.generalizeAndAssign chunkTypeLevel chunkFunctionType
    let kind = {
        T.semanticTree = body
        T.functionType = functionScheme
        T.ancestorModulePaths = Local.get ancestorModulePaths
        T.additionalGlobalEnv = Local.get additionalGlobalEnv
    }
    withSpan x.trivia.span kind, diagnostics :> _ seq, Local.get project

let chunk' env visitedSources project filePath source x = Local.runNotStruct { new ILocalScope<_> with
    member _.Invoke scope = chunkWithScope scope visitedSources project env filePath source x
}

let internal parse fs source =
    let source = fetchSourceContents fs source
    let scanner = Scanner.create source
    let block = Parser.sourceFile scanner
    let errors =
        match Scanner.currentErrors scanner with
        | [] -> [] :> _ seq
        | errors -> seq { for span, e in List.rev errors do Diagnostic.error span <| DiagnosticKind.ParseError e }

    struct(block, errors)

let checkSourceFileCached project filePath sourceFile = Local.runNotStruct { new ILocalScope<_> with
    member _.Invoke scope =
        let visitedSources = Local.create scope Set.empty
        checkSourceFileCached' visitedSources project filePath sourceFile
}
let checkSyntaxAndCache project filePath source syntax = Local.runNotStruct { new ILocalScope<_> with
    member _.Invoke scope =
        let sources = Local.create scope Set.empty
        checkSyntaxAndCache' sources project filePath source syntax
}
