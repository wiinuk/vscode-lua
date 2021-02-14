module LuaChecker.DocumentCheckers
open LuaChecker
open LuaChecker.CheckerEnv
open LuaChecker.TypeSystem
open LuaChecker.Primitives
open LuaChecker.Syntax
module D = Documents


[<AutoOpen>]
module private OperatorSemanticsHelpers =
    type L = LuaChecker.LeafFlags

    let withLeafFlags flags (D.Annotated(x, _)) = D.Annotated(x, { LeafSemantics.empty with leafFlags = flags })
    let withKeywordSemantics a = withLeafFlags L.Keyword a
    let withOperatorSemantics a = withLeafFlags L.Operator a
    let withType flags type' (D.Annotated(x, _)) =
        D.Annotated(x, {
            leafFlags = flags
            leafRare = { LeafSemanticsRare.empty with type' = ValueSome type' }
        })
    let withTypeParameterDefinitionSemantics type' a = withType (L.TypeParameter ||| L.Definition) type' a
    let withParameterDefinitionSemantics type' a = withType (L.Parameter ||| L.Definition) type' a
    let withTypeDefinition flags typeDefinition (D.Annotated(x, _)) =
        D.Annotated(x, {
            leafFlags = flags
            leafRare = {
                LeafSemanticsRare.empty with
                    typeDefinition = ValueSome typeDefinition
            }
        })
    let withDeclaration flags declaration (D.Annotated(x, _)) =
        D.Annotated(x, {
            leafFlags = flags
            leafRare = {
                LeafSemanticsRare.empty with
                    declaration = ValueSome declaration
            }
        })

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
        let struct(vs, instantiatedType) = Scheme.instantiate env.rare.noUpdate.typeSubst env.rare.typeLevel d
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

    let makeConsType (env: _ byref) span (t, m) =
        types(env.env).cons(t, m)
        |> Type.makeWithLocation (sourceLocation env.env span)

    let makeEmptyType (env: _ byref) span =
        types(env.env).empty
        |> Type.makeWithLocation (sourceLocation env.env span)

    let rec typeSign (env: _ byref) t =
        let struct(t', typeSign) = typeSignOrMultiType &env t
        struct(reportIfNotValueKind env.env t.trivia t', typeSign)

    and typeSignOrMultiType (env: _ byref) t =
        let struct(t', typeSign) =
            match t.kind with
            | D.WrappedType(l, t, r) -> wrappedType &env (l, t, r)
            | D.NilType nil -> nilType &env nil
            | D.NamedType(name, ts) -> namedType &env (name, ts)
            | D.ArrayType(et, l, r) -> arrayType &env t.trivia (et, l, r)
            | D.InterfaceType fs -> interfaceType &env t.trivia fs
            | D.FunctionType(``fun``, l, m1, r, c, m2) -> functionType &env t.trivia (``fun``, l, m1, r, c, m2)
            | D.ConstrainedType(t, sep, c) -> constrainedType &env (t, sep, c)

            | D.EmptyType(l, r) -> emptyType &env t.trivia (l, r)
            | D.SingleMultiType(l, t, s, r) -> singleMultiType &env (l, t, s, r)
            | D.VariadicType v -> variadicType &env v
            | D.MultiType2(p, c, ps) -> multiType2 &env (p, c, ps)

        t', Token.make t.trivia typeSign

    and wrappedType (env: _ byref) (l, t, r) =
        let struct(t, typeSign) = typeSignOrMultiType &env t
        t, D.WrappedType(withOperatorSemantics l, typeSign, withOperatorSemantics r)

    and emptyType (env: _ byref) span (l, r) =
        let t = makeEmptyType &env span
        t, D.EmptyType(withOperatorSemantics l, withOperatorSemantics r)

    and parameterRaw asMultiType (env: _ byref) parameter =
        let (D.Parameter(name, parameterTypeSign)) = parameter.kind

        let struct(parameterType, parameterTypeSign) = typeSignOrMultiType &env parameterTypeSign
        let name =
            match name with
            | None -> None
            | Some(name, colon) ->
                Some(
                    name |> withParameterDefinitionSemantics parameterType,
                    colon |> withOperatorSemantics
                )

        let parameterType =
            if asMultiType then
                match parameterTypeSign.kind with
                | D.VariadicType _ -> parameterType
                | _ ->
                    makeConsType &env parameter.trivia (
                        parameterType,
                        makeEmptyType &env parameter.trivia
                    )
            else
                // asValueType
                reportIfNotValueKind env.env parameter.trivia parameterType

        struct(
            parameterType,
            D.Parameter(name, parameterTypeSign)
            |> Token.make parameter.trivia
        )

    and singleMultiType (env: _ byref) (l, p, s, r) =
        let struct(parameter, parameterSign) = parameterRaw false &env p
        let typeSign =
            D.SingleMultiType(
                withOperatorSemantics l,
                parameterSign,
                withOperatorSemantics s,
                withOperatorSemantics r
            )
        parameter, typeSign

    and variadicType (env: _ byref) v =
        let struct(t, v) = varParam &env v
        t, D.VariadicType v

    and multiType2 (env: _ byref) (p1, D.Annotated(comma, _) & c, ps) =
        let struct(p1, pSign1) = parameterRaw false &env p1
        let struct(parametersType, parametersSign) = parameters &env ps

        makeConsType &env comma.trivia (p1, parametersType),
        D.MultiType2(pSign1, withOperatorSemantics c, parametersSign)

    and nilType (env: _ byref) (D.Annotated(nilToken, _) as nilSign) =
        let t = types(env.env).nil |> Type.makeWithLocation (sourceLocation env.env nilToken.trivia)
        let nilSign = D.NilType(nilSign |> withType (L.Type ||| L.Keyword) t)
        t, nilSign

    and namedType (env: _ byref) (D.Annotated(Name n as name, _) as typeName, ts) =
        let nameSpan = n.trivia.span
        match resolveType nameSpan n.kind env.env, n.kind, env.env.rare.selfType with

        // 型名を発見した
        | ValueSome d, _, _ -> resolvedNamedType &env false (typeName, ts) d
        | ValueNone, "self", ValueSome d -> resolvedNamedType &env true (typeName, ts) d

        | _ ->

        // 型名が見つからなかった
        match n.kind, ts with

        // 空型として扱う
        | "void", None ->
            let t =
                types(env.env).empty
                |> Type.makeWithLocation (sourceLocation env.env nameSpan)

            t, D.NamedType(typeName |> withType L.Keyword t, None)

        // それぞれ違う型変数として扱う
        // table<any,any> => table<?a,?b>
        | ("_" | "any"), None ->
            let t =
                newValueVarType env.env n.kind
                |> Type.makeWithLocation (sourceLocation env.env nameSpan)

            t, D.NamedType(typeName |> withType L.Keyword t, None)

        // 同じ名前は同じ型変数として扱う
        // table<T,T> => table<?a,?a>
        | TypeVarLikeName true, None ->
            let t = typeNameAsTypeVar &env name
            t, D.NamedType(typeName |> withType L.TypeParameter t, None)

        // 型名が見つからないエラーを報告
        | _ ->
            reportError env.env n.trivia.span (K.TypeNameNotFound n.kind)
            let t =
                newValueVarType env.env TypeNames.lostByError
                |> Type.makeWithLocation (sourceLocation env.env nameSpan)
            t, D.NamedType(typeName |> withType L.TypeParameter t, None)

    and resolvedNamedType (env: _ byref) isKeyword (D.Annotated(name, _) as typeName, ts) d =
        let struct(ts, genericArgumentsSign) = collectTypeArgs &env ts
        let t = buildTypeOfDefinition env.env name d ts
    
        let typeName = typeName |> withTypeDefinition (if isKeyword then L.Keyword else L.Type) d
        t, D.NamedType(typeName, genericArgumentsSign)

    and collectTypeArgs (env: _ byref) = function
        | None -> struct([], None)
        | Some(D.GenericArguments(l, SepBy(typeSign, ts), c, r)) ->
            let struct(t, argSign) = typeSignOrMultiType &env typeSign
            let struct(ts, argsSign) = collectTypeArgs' &env ts
            let argsSign =
                D.GenericArguments(
                    withOperatorSemantics l,
                    SepBy(argSign, argsSign),
                    Option.map withOperatorSemantics c,
                    withOperatorSemantics r
                )
            (t, typeSign.trivia)::ts, Some argsSign

    and collectTypeArgs' (env: _ byref) = function
        | [] -> [], []
        | (comma, typeSign)::argsSign ->

        let struct(t, typeSign) = typeSignOrMultiType &env typeSign
        let struct(ts, argsSign) = collectTypeArgs' &env argsSign
        let argsTail = (withOperatorSemantics comma, typeSign)::argsSign
        (t, typeSign.trivia)::ts, argsTail

    and arrayType (env: _ byref) span (elementTypeSign, l, r) =
        let struct(t, elementTypeSign) = typeSign &env elementTypeSign
        let types = types env.env
        let arrayTypeLocation = sourceLocation env.env span

        let t =
            types.table(types.number |> Type.makeWithLocation arrayTypeLocation, t)
            |> Type.makeWithLocation arrayTypeLocation

        t, D.ArrayType(elementTypeSign, withOperatorSemantics l, withOperatorSemantics r)

    and interfaceType (env: _ byref) span fs =
        let struct(keyToType, fs) = fields &env fs
        let t = InterfaceType keyToType |> Type.makeWithLocation (sourceLocation env.env span)
        t, D.InterfaceType fs

    and fields (env: _ byref) { kind = D.Fields(l, fs, c, r); trivia = span } = usingByrefAsRef &env (fun env ->
        let mutable keyToType = Map.empty
        let fields =
            fs
            |> SepBy.mapSep withOperatorSemantics (fun f -> Token.sourced f <| fun (D.Field(fieldKey, c, t)) ->
                let (D.Annotated(key, _)) = fieldKey

                let struct(t, typeSign) = typeSign &env.contents t

                match Map.tryFind key.kind keyToType with
                | ValueSome struct(_, otherSpan) ->
                    reportInfo env.contents.env key.trivia <| K.DuplicateFieldKey(key.kind, otherSpan)
                | _ -> ()

                keyToType <- Map.add key.kind (t, key.trivia) keyToType

                D.Field(
                    fieldKey |> withType L.Field t,
                    c |> withOperatorSemantics,
                    typeSign
                )
            )
        let keyToType = keyToType |> Map.map (fun _ struct(t, _) -> t)
        let fields =
            D.Fields(
                withOperatorSemantics l,
                fields,
                Option.map withOperatorSemantics c,
                withOperatorSemantics r
            )
            |> Token.make span
        keyToType, fields
        )
    and functionType (env: _ inref) span (``fun``, l, m1, r, c, resultTypeSign) =
        let mutable env = { env with implicitVariadicParameterType = None }
        let struct(m1, parametersSign) = functionParameters &env (l, m1, r)
        let types = types env.env
        let struct(m2, resultTypeSign) = typeSignOrMultiType &env resultTypeSign
        let m2 =
            if isMultiKind env.env m2 then m2 else
            types.cons(m2, types.empty |> Type.makeWithLocation m2.trivia)
            |> Type.makeWithLocation m2.trivia

        let t =
            types.fn(m1, m2)
            |> Type.makeWithLocation (sourceLocation env.env span)

        let functionTypeSign =
            D.FunctionType(
                withKeywordSemantics ``fun``,
                withOperatorSemantics l,
                parametersSign,
                withOperatorSemantics r,
                withOperatorSemantics c,
                resultTypeSign
            )

        t, functionTypeSign

    and functionParameters (env: _ byref) (D.Annotated(l, _), ps, D.Annotated(r, _)) =
        match ps with
        | Some ps ->
            let struct(t, parameters) = parameters &env ps
            t, Some parameters

        | _ ->
            makeEmptyType &env (Span.merge l.trivia r.trivia), None

    and parameters (env: _ byref) (D.Parameters(SepBy(p, ps))) = usingByrefAsRef &env (fun env ->
        let rec aux p0 = function

            // `(…, t0)` `(…, ...)`
            | [] ->
                let struct(parametersType, p0) = parameterRaw true &env.contents p0
                struct {| parametersType = parametersType; sign1 = p0; signs = []; signSpan = p0.trivia |}

            // `(…, t0, t1, …)`
            | (c1, p1)::ps ->
                let c1 = withOperatorSemantics c1
                let struct(t0, p0) = parameterRaw false &env.contents p0
                let ps = aux p1 ps
                let parametersSpan = Span.merge p0.trivia ps.signSpan
                let parametersType = makeConsType &env.contents parametersSpan (t0, ps.parametersType)
                struct
                    {|
                        parametersType = parametersType
                        sign1 = p0
                        signs = (c1, ps.sign1)::ps.signs
                        signSpan = parametersSpan
                    |}

        let ps = aux p ps
        let parametersSign = D.Parameters(SepBy(ps.sign1, ps.signs))
        ps.parametersType, parametersSign
        )

    and varParam (env: _ byref) { kind = D.VariadicTypeSign(n, dot3, c); trivia = span } =
        let typeEnv = typeEnv env.env
        let m = resolveMultiVar &env span n

        let elementTypeSign =
            match c with
            | None -> None
            | Some c ->

            let l = sourceLocation env.env c.trivia
            let struct(c', constraintTypeSign) = typeSign &env c
            let c' = c' |> MultiElementTypeConstraint |> Constraints.makeWithLocation l

            let n =
                match n with
                | Some(D.Annotated(Name n, _)) -> n.kind
                | _ -> TypeNames.implicitMultiVar

            let m' = newMultiVarTypeWith env.env n c' |> Type.makeWithLocation l
            match Type.unify typeEnv m m' with
            | ValueSome e -> reportError env.env c.trivia <| K.UnifyError e
            | _ -> ()

            Some constraintTypeSign

        let varSign =
            D.VariadicTypeSign(
                Option.map (withType L.TypeParameter m) n,
                withOperatorSemantics dot3,
                elementTypeSign
            )
            |> Token.make span

        m, varSign

    and constrainedType (env: _ byref) (t, sep, c) =
        let struct(t', typeSign) = typeSign &env t
        let struct(fs, fieldsSign) = fields &env c
        let l = sourceLocation env.env c.trivia
        let c' = Constraints.ofInterfaceType fs |> Constraints.makeWithLocation l
        let ct = newValueVarTypeWith env.env TypeNames.constrainedType c' |> Type.makeWithLocation l
        reportIfUnifyError env.env t.trivia t' ct

        let constrainedTypeSign = D.ConstrainedType(typeSign, withOperatorSemantics sep, fieldsSign)
        t', constrainedTypeSign

    let reportKindMismatchAndNewMissingType (TypeEnv types & env) span (expectedKind, actualKind) =
        let error =
            if actualKind = types.system.multiKind then K.UnexpectedMultiType
            elif expectedKind = types.system.multiKind then K.RequireMultiType
            else K.UnifyError(KindMismatch(actualKind, expectedKind))

        reportError env span error

        newVarType env TypeNames.lostByError expectedKind
        |> Type.makeWithLocation (sourceLocation env span)

    let ofTypeSignCore env expectedKind t =
        let mutable env = {
            TypeResolveEnv.env = env
            implicitVariadicParameterType = None
        }
        let struct(t', typeSign) = typeSignOrMultiType &env t

        let t' =
            match expectedKind with
            | ValueNone -> t'
            | ValueSome expectedKind ->

            let (TypeEnv types) = env.env
            let kind = Type.kind types.system t'
            if kind = expectedKind then t' else
            reportKindMismatchAndNewMissingType env.env t.trivia (expectedKind, kind)

        struct(t', typeSign)

    let ofTypeSign env t =
        ofTypeSignCore env (ValueSome(types(env).valueKind)) t

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module private Constraints =
    let ofConstraintSign env x =
        let mutable env = {
            TypeResolveEnv.env = env
            implicitVariadicParameterType = None
        }
        let struct(fs, fields) = Type.fields &env x
        struct(Constraints.ofInterfaceType fs, fields)

[<AutoOpen>]
module private Helpers =
    [<Struct>]
    type Converting<'From,'To> =
        | Pending of pending: 'From
        | Accepted of accepted: 'To

    let toPendingValues xs = xs |> List.map Pending
    let chooseConvertedValues xs = xs |> List.choose (function Accepted x -> Some x | _ -> None)

    let reportParseErrors env span es =
        for e in es do
            reportInfo env span <| DiagnosticKind.ParseError e

    let featureNameToKind = function
        | "require" -> DeclarationFeatures.GlobalRequire |> ValueSome
        | "package" -> DeclarationFeatures.GlobalPackage |> ValueSome
        | _ -> ValueNone

    let inline parseFeatureOfTags (|Parse|) env tags =
        match tags with
        | [] -> struct([], ValueNone)
        | _ ->

        let struct(tagsRev, firstFeatureTag) =
            tags
            |> List.fold (fun struct(tagsRev, firstFeatureTag) ({ kind = D.Tag(at, tail) } as tag) ->
                match tail.kind with
                | D.FeatureTag(feature, (D.Annotated(Name({ kind = Parse k as featureName } as name), _) as featureNameToken)) ->
                    match firstFeatureTag, k with

                    // 最初の有効な特徴タグを発見した
                    | ValueNone, ValueSome k ->

                        // タグに意味付け
                        let tag =
                            D.Tag(
                                at |> withKeywordSemantics,
                                D.FeatureTag(
                                    feature |> withKeywordSemantics,
                                    featureNameToken |> withKeywordSemantics
                                )
                                |> Token.make tail.trivia
                            )
                            |> Token.make tag.trivia

                        Accepted tag::tagsRev, ValueSome struct(tag, k)

                    // 特徴タグの名前が無効だった
                    | _, ValueNone ->
                        reportInfo env name.trivia.span <| DiagnosticKind.UnrecognizedFeatureName featureName
                        tagsRev, firstFeatureTag

                    // 複数の特徴タグが付いていた
                    | ValueSome(firstTag, _), ValueSome _ ->
                        reportInfo env tag.trivia <| DiagnosticKind.DuplicateTag("@_Feature", firstTag.trivia)
                        tagsRev, firstFeatureTag

                // 他のタグ
                | _ -> Pending tag::tagsRev, firstFeatureTag
            ) ([], ValueNone)

        let r = firstFeatureTag |> ValueOption.map (fun struct(_, r) -> r)
        List.rev tagsRev, r

    let declFeatureOfModifierTags env modifierTags =
        parseFeatureOfTags featureNameToKind env modifierTags

    let reportIfIncludesFeatureTag env modifierTags =
        parseFeatureOfTags (fun _ -> ValueNone) env modifierTags

    let unifyDeclAndReport env (Name({ kind = n; trivia = { span = nameSpan } } )) span newDecl oldDecl =

        // `require` や `package` などは警告付きで再宣言可能
        if oldDecl.declarationFeatures <> newDecl.declarationFeatures then
            let k = DiagnosticKind.RedeclarationOfSpecialGlobalVariable(n, oldDecl.declarationFeatures, newDecl.declarationFeatures)
            reportWarn env nameSpan k

        // 宣言済みの変数の型と一致しているか
        match Type.unify (typeEnv env) oldDecl.scheme newDecl.scheme with
        | ValueSome e -> reportError env span (DiagnosticKind.UnifyError e); false
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
    let unifyDecls env name span newType oldDecls = NonEmptyList.forall (unifyDeclAndReport env name span newType) oldDecls

    type TypeParameterBinding<'A> = {
        nameTokens: 'A Syntax.Name NonEmptyList
        varType: Type
    }
    let collectTypeParameterBindsCore (Types types as env) nameToBind typeParameter =
        let (D.Annotated(Name { kind = name; trivia = nameTrivia } as nameToken, _)), kind =
            match typeParameter.kind with
            | D.TypeParameter(name, _) -> name, types.valueKind
            | D.VariadicTypeParameter(name, _, _) -> name, types.multiKind

        let bind =
            match Map.tryFind name nameToBind with
            | ValueNone ->
                {
                    nameTokens = NonEmptyList.singleton nameToken

                    // 相互参照される制約を持つ型引数に対応するため、まず型制約なしで型変数を作る
                    // 後で制約付き型変数と型制約なしで型変数を単一化する
                    varType = newVarType env name kind |> Type.makeWithLocation (sourceLocation env nameTrivia.span)
                }
            | ValueSome bind ->

                // 型変数の種を単一化する
                // @generic T
                // @generic T...
                match Kind.unify (Type.kind types bind.varType) kind with
                | ValueSome e ->
                    let (Name n) = nameToken
                    reportError env n.trivia.span <| DiagnosticKind.UnifyError e

                | _ -> ()

                {
                    nameTokens = NonEmptyList.append bind.nameTokens (NonEmptyList.singleton nameToken)
                    varType = bind.varType
                }

        Map.add name bind nameToBind

    let foldTypeParameters folder state tags =
        tags
        |> List.fold (fun s tag ->
            match tag with
            | Pending { kind = D.Tag(_, { kind = D.GenericTag(_, ps) } ) } -> SepBy.fold folder s ps
            | _ -> s
        ) state

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

    let identifierName (D.Annotated(Name { kind = x }, _)) = x

    let unifyGenericTagConstraints env nameToBind (generic, parameters) =
        let generic = withKeywordSemantics generic

        let parameters =
            parameters
            |> SepBy.mapSep withOperatorSemantics (fun parameter -> Token.sourced parameter <| fun p ->
                let varName =
                    match p with
                    | D.TypeParameter(name, _)
                    | D.VariadicTypeParameter(name, _, _) -> identifierName name

                let varType = (Map.find varName nameToBind).varType

                match p with
                | D.TypeParameter(name, constrants) ->
                    let constraints =
                        match constrants with
                        | None -> None
                        | Some(comma, constraints) ->

                        let l = sourceLocation env constraints.trivia
                        let struct(c, constraints) = Constraints.ofConstraintSign env constraints
                        do
                            c
                            |> Constraints.makeWithLocation l
                            |> newValueVarTypeWith env varName
                            |> Type.makeWithLocation l
                            |> reportIfUnifyError env constraints.trivia varType

                        Some(
                            comma |> withLeafFlags L.Operator,
                            constraints
                        )

                    D.TypeParameter(
                        name |> withTypeParameterDefinitionSemantics varType,
                        constraints
                    )

                | D.VariadicTypeParameter(name, dot3, elementType) ->
                    let elementType =
                        match elementType with
                        | None -> None
                        | Some elementTypeSign ->
                            let l = sourceLocation env elementTypeSign.trivia
                            let struct(c, elementTypeSign) = Type.ofTypeSign env elementTypeSign
                            do
                                c
                                |> MultiElementTypeConstraint
                                |> Constraints.makeWithLocation l
                                |> newMultiVarTypeWith env varName
                                |> Type.makeWithLocation l
                                |> reportIfUnifyError env elementTypeSign.trivia varType

                            Some elementTypeSign

                    D.VariadicTypeParameter(
                        name |> withTypeParameterDefinitionSemantics varType,
                        dot3 |> withOperatorSemantics,
                        elementType
                    )
            )

        D.GenericTag(generic, parameters)

    let extendTypeEnvFromGenericTags modifierTags env =
        match modifierTags with
        | [] -> struct(env, [])
        | _ ->

        // まず制約なしの型変数を作る ( 相互参照される型に対応するため )
        //
        // `----@generic p: { x: n }, p: { y: n }, n, …` の場合
        // nameToBind = `Map ["p", (?p, [`{ x: n }`; `{ y: n }`]); "n", (?n, [])]`
        let nameToBind = foldTypeParameters (collectTypeParameterBindsCore env) Map.empty modifierTags

        // 型引数注釈がなかったので終わり
        if Map.isEmpty nameToBind then env, modifierTags else

        // 制約なしの型変数で型環境を拡張する
        // typeEnv = typeEnv @ ["p", ?p'; "n", ?n']
        let env = extendTypeEnvFromBind nameToBind env

        // 制約なしの型変数と一時的に作った型制約付き型変数を単一化する
        //
        // unify ?p (?p': { x: ?n })
        // unify ?p (?p'': { y: ?n })
        let tags =
            modifierTags
            |> List.map (function
                | Accepted _ as tag -> tag
                | Pending tag ->

                let (D.Tag(at, tail)) = tag.kind

                match tail.kind with
                | D.GenericTag(generic, parameters) ->
                    let at = withKeywordSemantics at
                    let genericTag = unifyGenericTagConstraints env nameToBind (generic, parameters) |> Token.make tail.trivia

                    D.Tag(at, genericTag)
                    |> Token.make tag.trivia
                    |> Accepted

                | _ -> Pending tag
            )
        env, tags

    let globalTag env modifierTags (at, ``global``, identifier, typeSign, tailSpan, tagSpan) =
        let (D.Annotated(Name({ kind = n; trivia = { span = nameSpan } }) as name, _)) = identifier

        let struct(modifierTags, features) = declFeatureOfModifierTags env modifierTags
        let features = features |> ValueOption.defaultValue DeclarationFeatures.NoFeatures

        let env' = enterTypeScope env
        let env' = enterTemporaryTypeVarNameScope env'
        let struct(env', modifierTags) = extendTypeEnvFromGenericTags modifierTags env'

        // グローバル変数宣言の型変数スコープはそのタグのみ
        let struct(t, typeSign) = Type.ofTypeSign env' typeSign
        let t = Scheme.generalize env.rare.noUpdate.typeSubst 0 t

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

        let ds =
            match Map.tryFind n g.Value.names with
            | ValueSome(NonEmptyList(_, ds') as dds') ->
                if unifyDecls env name typeSign.trivia d dds'
                then NonEmptyList(d, ds')
                else NonEmptyList.cons d dds'
            | _ ->

            match Map.tryFind n env.rare.noUpdate.defaultGlobalEnv.names with
            | ValueSome dds' -> unifyDecls env name typeSign.trivia d dds' |> ignore
            | _ -> ()

            NonEmptyList.singleton d

        g.Value <- { g.Value with names = Map.add n ds g.Value.names }

        let globalTagTail =
            D.GlobalTag(
                ``global`` |> withKeywordSemantics,
                identifier |> withDeclaration (L.Global ||| L.Variable ||| L.Declaration) d,
                typeSign
            )
            |> Token.make tailSpan

        let globalTag =
            D.Tag(
                at |> withKeywordSemantics,
                globalTagTail
            )
            |> Token.make tagSpan

        chooseConvertedValues modifierTags @ [globalTag]

    type BuildingType<'A,'typeName,'tempType,'fields,'tempEnv,'fieldSignsRev> = {
        typeName: 'typeName
        tempType: 'tempType
        fields: 'fields
        tempEnv: 'tempEnv
        isStringMetaTableIndex: bool

        tagsRev: 'A D.Tag list
    }
    let classTag env modifierTags (at, ``class``, identifier, parent, tagTailSpan, tagSpan) =
        let (D.Annotated(Name { kind = n; trivia = nameTrivia } as name, _)) = identifier

        let struct(modifierTags, isStringMetaTableIndex) =
            modifierTags
            |> parseFeatureOfTags (function "stringMetaTableIndex" -> ValueSome true | _ -> ValueNone) env

        let isStringMetaTableIndex = isStringMetaTableIndex |> ValueOption.defaultValue false

        // 自動型変数のためのスコープの開始
        let env = enterTemporaryTypeVarNameScope env
        let env = enterTypeScope env

        let struct(env, modifierTags) = extendTypeEnvFromGenericTags modifierTags env
        let t = newValueVarType env n |> Type.makeWithLocation (sourceLocation env nameTrivia.span)
        let d = {
            locations = [Location(env.rare.noUpdate.filePath, Name.measure name)]
            typeKind = TypeDefinitionKind.Alias t
        }
        let env = extendType n d env

        // self として登録
        let env = { env with rare = { env.rare with selfType = ValueSome d } }

        let parentSign =
            match parent with
            | None -> None
            | Some(colon, p) ->

            let parentName =
                match p.kind with
                | D.NamedType(D.Annotated(Name { kind = k }, _), _) -> k
                | _ -> TypeNames.classParent

            let struct(p', parentSign) = Type.ofTypeSign env p

            // 親がインターフェース型ならインターフェース制約とみなす
            let p' =
                match p'.kind with
                | InterfaceType fs ->
                    let l = sourceLocation env p.trivia
                    let c = Constraints.ofInterfaceType fs |> Constraints.makeWithLocation l
                    newValueVarTypeWith env parentName c |> Type.makeWithLocation l

                | _ -> p'

            reportIfUnifyError env (Name.measure name) t p'

            Some(
                withOperatorSemantics colon,
                parentSign
            )

        let classTagTail =
            D.ClassTag(
                ``class`` |> withKeywordSemantics,
                identifier |> withTypeDefinition L.Type d,
                parentSign
            )
            |> Token.make tagTailSpan

        let classTag =
            D.Tag(
                at |> withKeywordSemantics,
                classTagTail
            )
            |> Token.make tagSpan

        {
            typeName = name
            tempType = t
            fields = Map.empty
            tempEnv = env
            isStringMetaTableIndex = isStringMetaTableIndex

            tagsRev = classTag::List.rev (chooseConvertedValues modifierTags)
        }

    let fieldTag env modifierTags lastClass (at, field, visibility, identifier, typeSign, tailSpan, tagSpan) =
        match lastClass with
        | ValueNone -> reportInfo env tagSpan DiagnosticKind.FieldParentTagNotFound; ValueNone
        | ValueSome({ tempEnv = tempEnv } as lastClass) ->

        let struct(modifierTags, (ValueNone | ValueSome())) = reportIfIncludesFeatureTag tempEnv modifierTags

        // TODO: 現在 visibility は警告なしに無視されている
        let _ = visibility

        let (D.Annotated(key, _)) = identifier

        // 重複したキーをもつフィールドが存在していても問題はない ( 型の不一致エラーは出る ) が
        // ユーザーへの情報提供のため、ここでチェックする
        match Map.tryFind key.kind lastClass.fields with
        | ValueSome otherSpan -> reportInfo tempEnv key.trivia <| DiagnosticKind.DuplicateFieldKey(key.kind, otherSpan)
        | _ -> ()

        let struct(struct(fieldType, typeSign), modifierTags) =
            let tempEnv = enterTypeScope tempEnv
            let struct(tempEnv, modifierTags) = extendTypeEnvFromGenericTags modifierTags tempEnv
            Type.ofTypeSign tempEnv typeSign, modifierTags

        // フィールドに @generic で明示的に指定された型変数だけが汎用化される
        let fieldType = Scheme.generalize tempEnv.rare.noUpdate.typeSubst tempEnv.rare.typeLevel fieldType

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

        // フィールドに意味を付ける
        let fieldTail =
            D.FieldTag(
                field |> withKeywordSemantics,
                Option.map (withLeafFlags (L.Modification ||| L.Keyword)) visibility,
                identifier |> withType (L.Field ||| L.Definition) fieldType,
                typeSign
            )
            |> Token.make tailSpan

        let fieldSign =
            D.Tag(
                at |> withKeywordSemantics,
                fieldTail
            )
            |> Token.make tagSpan

        ValueSome {
            lastClass with
                fields = Map.add key.kind key.trivia lastClass.fields
                tagsRev = fieldSign::List.revAppend (chooseConvertedValues modifierTags) lastClass.tagsRev
        }

    /// `type … (a: C) … . a` で C がインターフェース制約で C の中に a がないとき、`type … . C` に変換する
    let interfaceConstraintToInterfaceType env nameSpan t =
        let struct(_, t') = Scheme.instantiate env.rare.noUpdate.typeSubst 1 t
        match t'.kind with
        | VarType(Subst.Find env.rare.noUpdate.typeSubst (Ok({ kind = VarType(Var(constraints = { kind = InterfaceConstraint fs } as c ) as r) }))) when Constraints.hasField c ->
            let varsEnv = {
                visitedVars = []
                other = {
                    level = 0
                    subst = env.rare.noUpdate.typeSubst
                }
            }
            let vs = Constraints.freeVars' varsEnv [] c
            match Assoc.tryFind r vs with
            | ValueNone -> InterfaceType fs |> Type.makeWithLocation (sourceLocation env nameSpan) |> Scheme.generalize env.rare.noUpdate.typeSubst 0
            | _ -> t
        | _ -> t

    let endClass lastClass =
        let Name({ kind = n } as nameToken) as name = lastClass.typeName
        let tempType = lastClass.tempType
        let env = lastClass.tempEnv

        // 自由変数はここで型引数に変換される
        // `---@class Vec4 : Vec2<T> @field z T @field w T` は
        // `---@generic T @class Vec4 : Vec2<T> @field z T @field w T` と同じ
        let generalizedType = Scheme.generalize env.rare.noUpdate.typeSubst 0 tempType

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

        List.rev lastClass.tagsRev

    let findLastTypeTag env (modifierTagsRev: _ byref) (lastTypeTag: _ byref) (tags: _ list) =
        for { kind = D.Tag(_, tail) } as tag in tags do
            match tail.kind with
            | D.TypeTag _ ->
                match lastTypeTag with
                | ValueSome struct(_, tag) -> reportInfo env tag.trivia <| DiagnosticKind.DuplicateTag("type", tag.trivia)
                | _ -> ()
                lastTypeTag <- ValueSome(List.rev modifierTagsRev, tag)
                modifierTagsRev <- []

            | _ -> modifierTagsRev <- tag::modifierTagsRev

    let typeTagToType env expectedKind = function
        | ValueSome struct(modifierTags, ({ kind = D.Tag(at, ({ kind = D.TypeTag(``type``, typeSign) } as typeTagTail)) } as typeTag)) ->
            let env' = enterTypeScope env
            let struct(env', modifierTags) = extendTypeEnvFromGenericTags (toPendingValues modifierTags) env'
            let struct(t, typeSign) = Type.ofTypeSignCore env' expectedKind typeSign
            let t = Scheme.generalize env.rare.noUpdate.typeSubst env.rare.typeLevel t

            let typeTagTail =
                D.TypeTag(
                    ``type`` |> withKeywordSemantics,
                    typeSign
                )
                |> Token.make typeTagTail.trivia

            let typeTag =
                D.Tag(
                    withKeywordSemantics at,
                    typeTagTail
                )
                |> Token.make typeTag.trivia

            let modifierTags = chooseConvertedValues modifierTags

            let span =
                match modifierTags with
                | [] -> typeTag.trivia
                | t::_ -> Span.merge t.trivia typeTag.trivia

            let tags =
                modifierTags @ [typeTag]
                |> Token.make span

            ValueSome struct(tags, t)

        | _ -> ValueNone

let findTypeTag (Types types & env) span struct(ds, es) =
    reportParseErrors env span es

    let mutable modifierTagsRev = []
    let mutable lastTypeTag = ValueNone
    for { kind = D.Document(_, tags) } in ds do
        findLastTypeTag env &modifierTagsRev &lastTypeTag tags

    typeTagToType env (ValueSome types.valueKind) lastTypeTag

let parseTagsToType env requiredKind tags =
    let mutable modifierTagsRev = []
    let mutable lastTypeTag = ValueNone
    findLastTypeTag env &modifierTagsRev &lastTypeTag tags
    typeTagToType env requiredKind lastTypeTag

let statementLevelTags env span struct(ds, es) =
    reportParseErrors env span es

    let mutable modifierTagsRev = []
    let mutable lastClass = ValueNone
    let tags = [
        for { kind = D.Document(_, tags) } in ds do
            for { kind = D.Tag(at, tail) } as tag in tags do
                match tail.kind with
                | D.ClassTag(``class``, identifier, parent) ->
                    match lastClass with
                    | ValueSome lastClass -> yield! endClass lastClass
                    | _ -> ()

                    lastClass <- ValueSome <| classTag env (List.rev modifierTagsRev) (at, ``class``, identifier, parent, tail.trivia, tag.trivia)
                    modifierTagsRev <- []

                | D.FieldTag(field, visibility, name, typeSign) ->
                    lastClass <- fieldTag env (List.rev modifierTagsRev) lastClass (at, field, visibility, name, typeSign, tail.trivia, tag.trivia)
                    modifierTagsRev <- []

                | D.GlobalTag(``global``, name, typeSign) ->
                    match lastClass with
                    | ValueSome lastClass -> yield! endClass lastClass
                    | _ -> ()

                    lastClass <- ValueNone
                    yield! globalTag env (List.rev modifierTagsRev) (at, ``global``, name, typeSign, tail.trivia, tag.trivia)
                    modifierTagsRev <- []


                | _ -> modifierTagsRev <- tag::modifierTagsRev

        match lastClass with
        | ValueSome lastClass -> yield! endClass lastClass
        | _ -> ()

        lastClass <- ValueNone
    ]
    let tags = tags |> Token.make (Span.list Source.measure tags)
    let modifierTags = List.rev modifierTagsRev
    struct(tags, modifierTags)
