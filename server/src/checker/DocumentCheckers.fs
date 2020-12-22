module LuaChecker.DocumentCheckers
open LuaChecker
open LuaChecker.CheckerEnv
open LuaChecker.TypeSystem
open LuaChecker.Primitives
open LuaChecker.Syntax
module D = Documents


[<Struct>]
type private TypeResolveEnv<'EnvScope,'RootScope> = {
    mutable implicitVariadicParameterType: Type option
    env: CheckerEnv<'EnvScope,'RootScope>
}
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module private Type =
    type private K = DiagnosticKind

    let getOrNewVar newVar i ts =
        match List.tryItem i ts with
        | None -> newVar()
        | Some struct(t, _) -> t

    let alignArity newVar expectedArity ts = [
        for i in 0..expectedArity-1 ->
            getOrNewVar newVar i ts
    ]
    let typeNameAsTypeVar (env: _ inref) (Name({ kind = name } as n)) =
        let vars = env.env.rare.temporaryTypeVarEnv
        match Map.tryFind name vars.Value with
        | ValueSome t -> t
        | _ ->

        let t =
            Type.newVar name env.env.rare.temporaryTypeVarLevel (types env.env).valueKind
            |> Type.makeWithLocation (sourceLocation env.env n.trivia.span)

        vars.Value <- Map.add name t vars.Value
        t

    let (|TypeVarLikeName|) name =
        String.length name = 1 ||
        (name.[0] = 'T' && not (System.Char.IsLower name.[1]))

    let getImplicitMultiVarType (env: _ byref) span =
        match env.implicitVariadicParameterType with
        | Some v -> v
        | None ->
            let v =
                newMultiVarType env.env TypeNames.implicitMultiVar
                |> Type.makeWithLocation (sourceLocation env.env span)
            env.implicitVariadicParameterType <- Some v
            v

    let resolveMultiVar (env: _ byref) span = function

        // 名前なしの複型変数 `...` は、暗黙的にスコープで共通の複型変数を指す
        | None -> getImplicitMultiVarType &env span

        // 名前付きの複型変数 `M...`
        | Some(D.Annotated(Name { kind = name; trivia = { span = nameSpan } }, _)) ->

        match resolveType nameSpan name env.env with
        | ValueSome d ->
            match d.typeKind with
            | TypeDefinitionKind.Variable(_, m)
            | TypeDefinitionKind.Alias m  -> reportIfNotMultiKind env.env nameSpan m
            | TypeDefinitionKind.System _ ->
                reportError env.env nameSpan K.RequireMultiType
                newMultiVarType env.env TypeNames.lostByError
                |> Type.makeWithLocation (sourceLocation env.env nameSpan)
        | _ ->

        let vars = env.env.rare.temporaryTypeVarEnv
        match Map.tryFind name vars.Value with

        // スコープにある名前だった
        | ValueSome t -> reportIfNotMultiKind env.env nameSpan t
        | _ ->

        // スコープにない名前だった
        let t =
            Type.newVar name env.env.rare.temporaryTypeVarLevel (types env.env).multiKind
            |> Type.makeWithLocation (sourceLocation env.env nameSpan)

        vars.Value <- Map.add name t vars.Value
        t

    let inline usingByrefAsRef (location: _ byref) scope =
        // TODO: pool
        let temp = ref location
        try scope temp
        finally location <- !temp

    let reportArityMismatch env (Name name) expectedArity actualArity =
        let e = K.TypeArityMismatch(expectedArity = expectedArity, actualArity = actualArity)
        reportError env name.trivia.span e

    let systemTableType (Types types as env) name typeArgs =
        match typeArgs with
        | [struct(k, _); struct(v, _)] when isValueKind env k && isValueKind env v -> types.table(k, v)
        | _ ->

        reportArityMismatch env name 2 (List.length typeArgs)

        let newVar() =
            newVarType env TypeNames.lostByError types.valueKind
            |> Type.makeWithLocation (sourceLocation env <| Name.measure name)

        types.table(
            getOrNewVar newVar 0 typeArgs,
            getOrNewVar newVar 1 typeArgs
        )

    let systemThreadType (Types types as env) name typeArgs =
        match typeArgs with
        | [struct(i, _); struct(o, _)] when isMultiKind env i && isMultiKind env o -> types.thread(i, o)
        | _ ->

        reportArityMismatch env name 2 (List.length typeArgs)
        let newVar() =
            newMultiVarType env TypeNames.lostByError
            |> Type.makeWithLocation (sourceLocation env <| Name.measure name)

        types.thread(
            getOrNewVar newVar 0 typeArgs,
            getOrNewVar newVar 1 typeArgs
        )

    let unifyApplications env name typeParameterToType typeWithSpans =
        let rec aux remainingVs remainingTs =
            match remainingVs, remainingTs with
            | [], [] -> ()
            | struct(_, v)::vs, struct(t, span)::ts ->
                match Type.unify (typeEnv env) v t with
                | ValueSome e -> reportError env span <| K.UnifyError e
                | _ -> ()

                aux vs ts

            | _ ->
                reportArityMismatch env name (List.length typeParameterToType) (List.length typeWithSpans)

        aux typeParameterToType typeWithSpans

    let buildTypeOfAliasDefinition env name d typeArgs =
        let struct(vs, instantiatedType) = Scheme.instantiate env.rare.typeLevel d
        match vs, typeArgs with
        | [], [] -> instantiatedType
        | _ ->
            unifyApplications env name vs typeArgs
            instantiatedType

    let reportErrorIfHasTypeArgs env name = function
        | [] -> ()
        | ts -> reportArityMismatch env name 0 (List.length ts)

    let buildTypeOfDefinition env name d typeArgs =
        match d.typeKind with
        | TypeDefinitionKind.System c ->
            let types = types env
            match c with
            | SystemTypeCode.Boolean -> reportErrorIfHasTypeArgs env name typeArgs; types.boolean
            | SystemTypeCode.Nil -> reportErrorIfHasTypeArgs env name typeArgs; types.nil
            | SystemTypeCode.Number -> reportErrorIfHasTypeArgs env name typeArgs; types.number
            | SystemTypeCode.String -> reportErrorIfHasTypeArgs env name typeArgs; types.string
            | SystemTypeCode.Table -> systemTableType env name typeArgs
            | SystemTypeCode.Thread -> systemThreadType env name typeArgs
            |> Type.makeWithLocation (sourceLocation env (Name.measure name))

        | TypeDefinitionKind.Alias d
        | TypeDefinitionKind.Variable(_, d) ->
            if isMultiKind env d then
                // `M...<T>`
                let (Name { trivia = { span = nameSpan } }) = name
                reportError env nameSpan <| K.UnexpectedMultiType
                newValueVarType env TypeNames.lostByError
                |> Type.makeWithLocation (sourceLocation env nameSpan)
            else
                buildTypeOfAliasDefinition env name d typeArgs

    let splitLastVarOrReport (env: _ byref) ps = usingByrefAsRef &env (fun env ->
        let struct(psRev, v) =
            ps
            |> List.fold (fun struct(psRev, lastVar) { kind = D.Parameter(_, t) } ->
                match t.kind with
                | D.VariadicType v ->
                    match lastVar with
                    | Some lastVar -> reportError env.contents.env lastVar.trivia K.UnexpectedMultiType
                    | _ -> ()
                    psRev, Some v

                | _ -> t::psRev, lastVar
            ) ([], None)

        List.rev psRev, v
    )

    let rec typeSign (env: _ byref) t =
        let t' = typeSignOrMultiType &env t
        reportIfNotValueKind env.env t.trivia t'

    and functionParameters (env: _ byref) (D.Annotated(l, _), ps, D.Annotated(r, _)) =
        let ts, v =
            match ps with
            | None -> [], None
            | Some(D.Parameters ps) -> splitLastVarOrReport &env (SepBy.toList ps)

        parameters &env (Span.merge l.trivia r.trivia) (ts, v)

    and typeSignOrMultiType (env: _ byref) t =
        match t.kind with
        | D.WrappedType(_, t, _) -> typeSignOrMultiType &env t
        | D.NamedType(name, ts) -> namedType &env (name, ts)
        | D.ArrayType(et, _, _) -> arrayType &env t.trivia et
        | D.InterfaceType fs -> interfaceType &env t.trivia fs
        | D.FunctionType(_, l, m1, r, _, m2) -> functionType &env t.trivia (l, m1, r) m2
        | D.ConstrainedType(t, _, c) -> constrainedType &env t c

        | D.EmptyType _ -> parameters &env t.trivia ([], None)
        | D.SingleMultiType(_, { kind = D.Parameter(_, t) }, _, _) -> parameters &env t.trivia ([t], None)
        | D.VariadicType v -> parameters &env t.trivia ([], Some v)
        | D.MultiType2(p, _, D.Parameters ps) -> parameters &env t.trivia (splitLastVarOrReport &env (p::SepBy.toList ps))

    and parameters (env: _ byref) span (ts, v) = usingByrefAsRef &env (fun env ->
        let last = varParam &env.contents span v
        List.foldBack (fun t m ->
            let t' = typeSign &env.contents t
            let l = sourceLocation env.contents.env t.trivia
            types(env.contents.env).cons(t', m) |> Type.makeWithLocation l
        ) ts last
        )

    and collectTypeArgs' (env: _ byref) acc = function
        | [] -> List.rev acc
        | (_, t)::ts ->
            let t' = typeSignOrMultiType &env t
            collectTypeArgs' &env (struct(t', t.trivia)::acc) ts

    and collectTypeArgs (env: _ byref) = function
        | None -> []
        | Some(D.GenericArguments(_, SepBy(t, ts), _, _)) ->
            let t' = typeSignOrMultiType &env t
            collectTypeArgs' &env [struct(t', t.trivia)] ts

    and namedType (env: _ byref) (D.Annotated(Name n as name, _), ts) =
        let nameSpan = n.trivia.span
        match resolveType nameSpan n.kind env.env, n.kind, env.env.rare.selfType with
        | ValueSome d, _, _
        | ValueNone, "self", ValueSome d ->

            // 型名を発見した
            let ts = collectTypeArgs &env ts
            buildTypeOfDefinition env.env name d ts

        | _ ->

        // 型名が見つからなかった
        match n.kind, ts with

        // 空型として扱う
        | "void", None ->
            types(env.env).empty |> Type.makeWithLocation (sourceLocation env.env nameSpan)

        // それぞれ違う型変数として扱う
        // table<any,any> => table<?a,?b>
        | ("_" | "any"), None ->
            newValueVarType env.env n.kind
            |> Type.makeWithLocation (sourceLocation env.env nameSpan)

        // 同じ名前は同じ型変数として扱う
        // table<T,T> => table<?a,?a>
        | TypeVarLikeName true, None ->
            typeNameAsTypeVar &env name

        // 型名が見つからないエラーを報告
        | _ ->
            reportError env.env n.trivia.span (K.TypeNameNotFound n.kind)
            newValueVarType env.env TypeNames.lostByError
            |> Type.makeWithLocation (sourceLocation env.env nameSpan)

    and arrayType (env: _ byref) span elementType =
        let elementType = typeSign &env elementType
        let types = types env.env
        let l = sourceLocation env.env span

        types.table(types.number |> Type.makeWithLocation l, elementType)
        |> Type.makeWithLocation l

    and interfaceType (env: _ byref) span fs =
        let keyToType = fields &env fs
        InterfaceType keyToType |> Type.makeWithLocation (sourceLocation env.env span)

    and fields (env: _ byref) { kind = D.Fields(_, fs, _, _) } = usingByrefAsRef &env (fun env ->
        fs
        |> SepBy.fold (fun keyToType { kind = D.Field({ kind = k; trivia = ks }, _, t) } ->
            let t = typeSign &env.contents t

            match Map.tryFind k keyToType with
            | ValueSome struct(_, otherSpan) ->
                reportInfo env.contents.env ks <| K.DuplicateFieldKey(k, otherSpan)
            | _ -> ()

            Map.add k (t, ks) keyToType
        ) Map.empty
        |> Map.map (fun _ struct(t, _) -> t)
        )

    and functionType (env: _ inref) span (l, m1, r) m2 =
        let mutable env = { env with implicitVariadicParameterType = None }
        let m1 = functionParameters &env (l, m1, r)
        let types = types env.env
        let m2 = typeSignOrMultiType &env m2
        let m2 =
            if isMultiKind env.env m2 then m2 else
            types.cons(m2, types.empty |> Type.makeWithLocation m2.trivia)
            |> Type.makeWithLocation m2.trivia

        types.fn(m1, m2)
        |> Type.makeWithLocation (sourceLocation env.env span)

    and varParam (env: _ byref) span v =
        let { system = types } as typeEnv = typeEnv env.env
        match v with
        | None -> types.empty |> Type.makeWithLocation (sourceLocation env.env span)
        | Some { kind = D.VariadicTypeSign(n, _, c); trivia = span } ->

        let m = resolveMultiVar &env span n

        match c with
        | None -> ()
        | Some c ->
            let l = sourceLocation env.env c.trivia
            let c' = typeSign &env c |> MultiElementTypeConstraint |> Constraints.makeWithLocation l
            let n =
                match n with
                | Some(D.Annotated(Name n, _)) -> n.kind
                | _ -> TypeNames.implicitMultiVar

            let m' = newMultiVarTypeWith env.env n c' |> Type.makeWithLocation l
            match Type.unify typeEnv m m' with
            | ValueSome e -> reportError env.env c.trivia <| K.UnifyError e
            | _ -> ()
        m

    and constrainedType (env: _ byref) t c =
        let t' = typeSign &env t
        let fs = fields &env c
        let l = sourceLocation env.env c.trivia
        let c' = Constraints.ofInterfaceType fs |> Constraints.makeWithLocation l
        let ct = newValueVarTypeWith env.env TypeNames.constrainedType c' |> Type.makeWithLocation l
        reportIfUnifyError env.env t.trivia t' ct
        t'

    let ofTypeSign env t =
        let mutable env = {
            TypeResolveEnv.env = env
            implicitVariadicParameterType = None
        }
        typeSign &env t

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module private Constraints =
    let ofConstraintSign env x =
        let mutable env = {
            TypeResolveEnv.env = env
            implicitVariadicParameterType = None
        }
        Constraints.ofInterfaceType <| Type.fields &env x

[<AutoOpen>]
module private Helpers =
    let reportParseErrors env span es =
        for e in es do
            reportInfo env span <| DiagnosticKind.ParseError e

    let featureNameToKind = function
        | "require" -> DeclarationFeatures.GlobalRequire |> ValueSome
        | "package" -> DeclarationFeatures.GlobalPackage |> ValueSome
        | _ -> ValueNone

    let inline parseFeatureOfTags (|Parse|) env tags =
        match tags with
        | [] -> ValueNone
        | _ ->

        tags
        |> List.fold (fun nearestKind ({ kind = D.Tag(_, tail) } as tag) ->
            match tail.kind with
            | D.FeatureTag(_, D.Annotated(Name({ kind = Parse k as featureName } as name), _)) ->
                match nearestKind, k with
                | ValueNone, ValueSome k -> ValueSome struct(tag, k)
                | _, ValueNone ->
                    reportInfo env name.trivia.span <| DiagnosticKind.UnrecognizedFeatureName featureName
                    nearestKind

                | ValueSome struct(nearestTag, _), ValueSome _ ->
                    reportInfo env tag.trivia <| DiagnosticKind.DuplicateTag nearestTag
                    nearestKind
            | _ -> nearestKind
        ) ValueNone
        |> ValueOption.map (fun struct(_, k) -> k)

    let declFeatureOfModifierTags env modifierTags =
        parseFeatureOfTags featureNameToKind env modifierTags |> ValueOption.defaultValue DeclarationFeatures.NoFeatures

    let reportIfIncludesFeatureTag env modifierTags =
        parseFeatureOfTags (fun _ -> ValueNone) env modifierTags |> ValueOption.defaultValue ()

    let unifyDeclAndReport env (Name({ kind = n; trivia = { span = nameSpan } } )) typeSign newDecl oldDecl =

        // `require` や `package` などは警告付きで再宣言可能
        if oldDecl.declarationFeatures <> newDecl.declarationFeatures then
            let k = DiagnosticKind.RedeclarationOfSpecialGlobalVariable(n, oldDecl.declarationFeatures, newDecl.declarationFeatures)
            reportWarn env nameSpan k

        // 宣言済みの変数の型と一致しているか
        match Type.unify (typeEnv env) oldDecl.scheme newDecl.scheme with
        | ValueSome e -> reportError env typeSign.trivia (DiagnosticKind.UnifyError e); false
        | _ -> true

    let unifyTypeDeclAndReport env (Name({ trivia = { span = nameSpan } } )) newType oldDecl =
        match oldDecl.typeKind with

        // 基本型は再宣言できない
        | TypeDefinitionKind.System c ->
            let k = DiagnosticKind.RedeclarationOfBasicType c
            reportError env nameSpan k
            false

        | TypeDefinitionKind.Alias oldType ->

            // 宣言済みの変数の型と一致しているか
            match Type.unify (typeEnv env) oldType newType with
            | ValueSome e -> reportError env nameSpan (DiagnosticKind.UnifyError e); false
            | _ -> true

        // 型変数と同名の型は宣言できない
        // NOTE: このパターンに一致する構文は存在しない?
        | TypeDefinitionKind.Variable(name, _) ->
            let k = DiagnosticKind.RedeclarationOfTypeVariable(name, oldDecl.locations)
            reportError env nameSpan k
            false

    let unifyTypeDecls env name newType oldDecls = NonEmptyList.forall (unifyTypeDeclAndReport env name newType) oldDecls
    let unifyDecls env name typeSign newType oldDecls = NonEmptyList.forall (unifyDeclAndReport env name typeSign newType) oldDecls

    type TypeParameterBinding = {
        nameTokens: HEmpty Syntax.Name NonEmptyList
        varType: Type
        constraints: Choice<HEmpty D.Reserved * HEmpty D.TypeConstraints, HEmpty D.TypeSign> list
    }
    let consOption c cs = match c with None -> cs | Some c -> c::cs
    let collectTypeParameterBindsCore env kind nameToBind (D.Annotated(Name { kind = name; trivia = nameTrivia } as nameToken, _), c) =
        let bind =
            match Map.tryFind name nameToBind with
            | ValueNone ->
                {
                    nameTokens = NonEmptyList.singleton nameToken

                    // 相互参照される制約を持つ型引数に対応するため、まず型制約なしで型変数を作る
                    // 後で制約付き型変数と型制約なしで型変数を単一化する
                    varType = newVarType env name kind |> Type.makeWithLocation (sourceLocation env nameTrivia.span)

                    constraints = Option.toList c
                }
            | ValueSome bind ->

                // 型変数の種を単一化する
                // @generic T
                // @generic T...
                match unifyKind (Type.kind (typeEnv env) bind.varType) kind with
                | ValueSome e ->
                    let (Name n) = nameToken
                    reportError env n.trivia.span <| DiagnosticKind.UnifyError e

                | _ -> ()

                {
                    nameTokens = NonEmptyList.append bind.nameTokens (NonEmptyList.singleton nameToken)
                    varType = bind.varType
                    constraints = consOption c bind.constraints
                }

        Map.add name bind nameToBind

    let foldTypeParameters folder state tags =
        tags
        |> List.fold (fun s { kind = D.Tag(_, tail) } ->
            match tail.kind with
            | D.GenericTag(_, ps) -> SepBy.fold folder s ps
            | _ -> s
        ) state

    let collectEmptyBinds (Types types as env) map tags =
        tags
        |> foldTypeParameters (fun map p ->
            match p.kind with
            | D.TypeParameter(name, c) -> collectTypeParameterBindsCore env types.valueKind map (name, Option.map Choice1Of2 c)
            | D.VariadicTypeParameter(name, _, c) -> collectTypeParameterBindsCore env types.multiKind map (name, Option.map Choice2Of2 c)
        ) map

    let extendTypeEnvFromBind nameToBind env =
        nameToBind
        |> Map.fold (fun env n bind ->
            let locations = bind.nameTokens |> NonEmptyList.toList |> List.map (fun (Name n) -> Location(env.rare.noUpdate.filePath, n.trivia.span))
            let kind = TypeDefinitionKind.Variable(n, bind.varType)
            let definition = {
                locations = locations
                typeKind = kind
            }
            extendType n definition env
        ) env

    let extendTypeEnvFromGenericTags modifierTags env =
        match modifierTags with
        | [] -> env
        | _ ->

        // まず制約なしの型変数を作る ( 相互参照される型に対応するため )
        //
        // `type p: { x: n }, p: { y: n }, n. …` の場合
        // nameToBind = `Map ["p", (?p, ["{ x: n }"; "{ y: n }"]`); "n", (?n, [])]`
        let nameToBind = collectEmptyBinds env Map.empty <| List.rev modifierTags

        // 型引数注釈がなかったので終わり
        if Map.isEmpty nameToBind then env else

        // 制約なしの型変数で型環境を拡張する
        // typeEnv = typeEnv @ ["p", ?p'; "n", ?n']
        let env = extendTypeEnvFromBind nameToBind env

        // 制約なしの型変数と一時的に作った型制約付き型変数を単一化する
        //
        // unify ?p (?p': { x: ?n })
        // unify ?p (?p'': { y: ?n })
        for kv in nameToBind do
            let bind = kv.Value
            let (Name { kind = varName }) = bind.nameTokens |> NonEmptyList.head
            for c in bind.constraints do
                let span =
                    match c with
                    | Choice1Of2(_, c) -> c.trivia
                    | Choice2Of2 e -> e.trivia

                let v' =
                    match c with
                    | Choice1Of2(_, c) ->
                        let l = sourceLocation env c.trivia
                        let c' = Constraints.ofConstraintSign env c |> Constraints.makeWithLocation l
                        newValueVarTypeWith env varName c' |> Type.makeWithLocation l

                    | Choice2Of2 e ->
                        let l = sourceLocation env e.trivia
                        let c = Type.ofTypeSign env e |> MultiElementTypeConstraint |> Constraints.makeWithLocation l
                        newMultiVarTypeWith env varName c |> Type.makeWithLocation l

                reportIfUnifyError env span bind.varType v'
        env

    let globalTag env modifierTags (D.Annotated(Name({ kind = n; trivia = { span = nameSpan } }) as name, _), typeSign) =
        let features = declFeatureOfModifierTags env modifierTags
        let env' = enterTypeScope env
        let env' = enterTemporaryTypeVarNameScope env'
        let env' = extendTypeEnvFromGenericTags modifierTags env'

        // グローバル変数宣言の型変数スコープはそのタグのみ
        let t = Type.ofTypeSign env' typeSign
        let t = Scheme.generalize 0 t

        let l = Some <| Location(env.rare.noUpdate.filePath, nameSpan)
        let d = {
            declarationFeatures = features
            declarationScope = IdentifierScope.Global
            declarationKind = IdentifierKind.Variable
            declarationRepresentation = IdentifierRepresentation.Declaration
            scheme = t
            location = l
        }
        let g = env.rare.noUpdate.additionalGlobalEnv

        let d =
            match Map.tryFind n g.Value.names with
            | ValueSome(NonEmptyList(_, ds') as dds') ->
                if unifyDecls env name typeSign d dds'
                then NonEmptyList(d, ds')
                else NonEmptyList.cons d dds'
            | _ ->

            match Map.tryFind n env.rare.noUpdate.defaultGlobalEnv.names with
            | ValueSome dds' -> unifyDecls env name typeSign d dds' |> ignore
            | _ -> ()

            NonEmptyList.singleton d

        g.Value <- { g.Value with names = Map.add n d g.Value.names }

    type BuildingType<'typeName,'tempType,'fields,'tempEnv> = {
        typeName: 'typeName
        tempType: 'tempType
        fields: 'fields
        tempEnv: 'tempEnv
        isStringMetaTableIndex: bool
    }
    let classTag env modifierTags (D.Annotated(Name { kind = n; trivia = nameTrivia } as name, _), parent) =
        let isStringMetaTableIndex =
            parseFeatureOfTags (function "stringMetaTableIndex" -> ValueSome true | _ -> ValueNone) env modifierTags
            |> ValueOption.defaultValue false

        // 自動型変数のためのスコープの開始
        let env = enterTemporaryTypeVarNameScope env
        let env = enterTypeScope env

        let env = extendTypeEnvFromGenericTags modifierTags env
        let t = newValueVarType env n |> Type.makeWithLocation (sourceLocation env nameTrivia.span)
        let d = {
            locations = [Location(env.rare.noUpdate.filePath, Name.measure name)]
            typeKind = TypeDefinitionKind.Alias t
        }
        let env = extendType n d env

        // self として登録
        let env = { env with rare = { env.rare with selfType = ValueSome d } }

        match parent with
        | None -> ()
        | Some(_, p) ->
            let parentName =
                match p.kind with
                | D.NamedType(D.Annotated(Name { kind = k }, _), _) -> k
                | _ -> TypeNames.classParent

            let p' = Type.ofTypeSign env p

            // 親がインターフェース型ならインターフェース制約とみなす
            let p' =
                match p'.kind with
                | InterfaceType fs ->
                    let l = sourceLocation env p.trivia
                    let c = Constraints.ofInterfaceType fs |> Constraints.makeWithLocation l
                    newValueVarTypeWith env parentName c |> Type.makeWithLocation l

                | _ -> p'

            reportIfUnifyError env (Name.measure name) t p'

        {
            typeName = name
            tempType = t
            fields = Map.empty
            tempEnv = env
            isStringMetaTableIndex = isStringMetaTableIndex
        }

    let fieldTag env modifierTags lastClass tagSpan (visibility, key, typeSign) =
        match lastClass with
        | ValueNone -> reportInfo env tagSpan DiagnosticKind.FieldParentTagNotFound; ValueNone
        | ValueSome({ tempEnv = tempEnv } as lastClass) ->

        reportIfIncludesFeatureTag tempEnv modifierTags

        // TODO: 現在 visibility は警告なしに無視されている
        let _ = visibility

        // 重複したキーをもつフィールドが存在していても問題はない ( 型の不一致エラーは出る ) が
        // ユーザーへの情報提供のため、ここでチェックする
        match Map.tryFind key.kind lastClass.fields with
        | ValueSome otherSpan -> reportInfo tempEnv key.trivia <| DiagnosticKind.DuplicateFieldKey(key.kind, otherSpan)
        | _ -> ()

        let fieldType =
            let tempEnv = enterTypeScope tempEnv
            let tempEnv = extendTypeEnvFromGenericTags modifierTags tempEnv
            Type.ofTypeSign tempEnv typeSign

        // フィールドに @generic で明示的に指定された型変数だけが汎用化される
        let fieldType = Scheme.generalize tempEnv.rare.typeLevel fieldType

        // 現在交差型はないので、
        // 変換中の型は、もしインターフェース型ならインターフェース制約付き型変数に変換する
        // フィールドのキーと型は、1要素のインターフェース型制約付き型変数に変換する
        // そして型変数同士を単一化する
        //
        // 変換中の型: `{ x: number }`
        // フィールドのキー: `y`
        // フィールドの型: `number`
        // として
        // `{ x: number } & { y: number }` の代わりに
        // 変換中の型 `{ x: number }` を `?a: { x: number }` に変換し
        // `unify (?a: { x: number }) (?b: { y: number })` を行い
        // 変換中の型が `?a: { x: number, y: number }` になる
        let tempType = lastClass.tempType

        /// `{ key: fieldType }`
        let keyValueType =
            let keyValueName = TypeNames.fromFieldKey key.kind |> ValueOption.defaultValue TypeNames.fieldKeyValueInterface
            let fs = Map.add key.kind fieldType Map.empty
            let l = sourceLocation env tagSpan
            let c = Constraints.ofInterfaceType fs |> Constraints.makeWithLocation l
            newValueVarTypeWith tempEnv keyValueName c |> Type.makeWithLocation l

        // ここで
        // 親型との不一致 `---@class X : number @field f1 string` や
        // フィールド型の不一致 `---@class Y : { f1: number } @field f1 string`
        // などが報告される
        reportIfUnifyError tempEnv typeSign.trivia tempType keyValueType

        ValueSome {
            typeName = lastClass.typeName
            tempType = tempType
            fields = Map.add key.kind key.trivia lastClass.fields
            tempEnv = tempEnv
            isStringMetaTableIndex = lastClass.isStringMetaTableIndex
        }

    /// `type … (a: C) … . a` で C がインターフェース制約で C の中に a がないとき、`type … . C` に変換する
    let interfaceConstraintToInterfaceType env nameSpan t =
        let struct(_, t') = Scheme.instantiate 1 t
        match t'.kind with
        | VarType({ target = Var(_, ({ kind = InterfaceConstraint fs } as c)) } as r) when Constraints.hasField c ->
            let varsEnv = {
                visitedVars = []
                other = { level = 0 }
            }
            let vs = Constraints.freeVars' varsEnv [] c
            match Assoc.tryFindBy VarType.physicalEquality r vs with
            | ValueNone -> InterfaceType fs |> Type.makeWithLocation (sourceLocation env nameSpan) |> Scheme.generalize 0
            | _ -> t
        | _ -> t

    let endClass lastClass =
        let Name({ kind = n } as nameToken) as name = lastClass.typeName
        let tempType = lastClass.tempType
        let env = lastClass.tempEnv

        // 自由変数はここで型引数に変換される
        // `---@class Vec4 : Vec2<T> @field z T @field w T` は
        // `---@generic T @class Vec4 : Vec2<T> @field z T @field w T` と同じ
        let generalizedType = Scheme.generalize 0 tempType

        let generalizedType = interfaceConstraintToInterfaceType env nameToken.trivia.span generalizedType

        let g = env.rare.noUpdate.additionalGlobalEnv

        let d = {
            typeKind = TypeDefinitionKind.Alias generalizedType
            locations = [Location(env.rare.noUpdate.filePath, nameToken.trivia.span)]
        }
        let d =
            match Map.tryFind n g.Value.types with
            | ValueSome(NonEmptyList(_, ds') as dds') ->
                if unifyTypeDecls env name generalizedType dds'
                then NonEmptyList(d, ds')
                else NonEmptyList.cons d dds'
            | _ ->

            match Map.tryFind n env.rare.noUpdate.defaultGlobalEnv.types with
            | ValueSome dds' -> unifyTypeDecls env name generalizedType dds' |> ignore
            | _ -> ()

            NonEmptyList.singleton d

        g.Value <- { g.Value with types = Map.add n d g.Value.types }

        // 文字列の追加インターフェースを表す型を追加する
        if lastClass.isStringMetaTableIndex then
            g
            |> Local.modify (fun g ->
                { g with stringMetaTableIndexType = g.stringMetaTableIndexType @ [generalizedType] }
            )

    let processRemainingModifierTags env modifierTags =
        for { kind = D.Tag(_, tail) } as tag in modifierTags do
            match tail.kind with

            // 親構文への注釈
            | D.FeatureTag(_, (D.Annotated(Name { kind = featureName } as name, _))) ->
                reportInfo env (Name.measure name) <| DiagnosticKind.UnrecognizedFeatureName featureName

            | D.GenericTag _ ->
                reportInfo env tag.trivia DiagnosticKind.GenericTagParentSyntaxNotFound

            // TODO: 親構文を修飾する @type を実装する
            | D.TypeTag _ ->
                reportInfo env tag.trivia DiagnosticKind.TypeTagParentSyntaxNotFound

            | D.ClassTag _
            | D.FieldTag _
            | D.GlobalTag _
            | D.UnknownTag _
                -> ()

let findTypeTag env span struct(ds, es) =
    reportParseErrors env span es

    let mutable modifierTags = []
    let mutable lastTypeTag = ValueNone
    for { kind = D.Document(_, tags) } in ds do
        for { kind = D.Tag(_, tail) } as tag in tags do
            match tail.kind with
            | D.TypeTag(_, t) ->
                match lastTypeTag with
                | ValueSome struct(_, span, _) -> reportInfo env span <| DiagnosticKind.DuplicateTag tag
                | _ -> ()
                lastTypeTag <- ValueSome(modifierTags, tag.trivia, t)
                modifierTags <- []

            | _ -> modifierTags <- tag::modifierTags

    match lastTypeTag with
    | ValueNone -> ValueNone
    | ValueSome(modifierTags, _, typeSign) ->
        let env' = enterTypeScope env
        let env' = extendTypeEnvFromGenericTags modifierTags env'
        let t = Type.ofTypeSign env' typeSign
        let t = Scheme.generalize env.rare.typeLevel t
        ValueSome struct(typeSign, t)

let statementLevelTags env span struct(ds, es) =
    reportParseErrors env span es

    let mutable modifierTags = []
    let mutable lastClass = ValueNone
    for { kind = D.Document(_, tags) } in ds do
        for { kind = D.Tag(_, tail) } as tag in tags do
            match tail.kind with
            | D.GlobalTag(_, name, typeSign) ->
                ValueOption.iter endClass lastClass
                lastClass <- ValueNone
                globalTag env modifierTags (name, typeSign)
                modifierTags <- []

            | D.ClassTag(_, name, parent) ->
                ValueOption.iter endClass lastClass
                lastClass <- ValueSome <| classTag env modifierTags (name, parent)
                modifierTags <- []

            | D.FieldTag(_, visibility, name, typeSign) ->
                lastClass <- fieldTag env modifierTags lastClass tag.trivia (visibility, name, typeSign)
                modifierTags <- []

            | _ -> modifierTags <- tag::modifierTags

    ValueOption.iter endClass lastClass
    lastClass <- ValueNone
    processRemainingModifierTags env modifierTags
