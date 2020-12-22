module LuaChecker.DocumentCheckers
open LuaChecker
open LuaChecker.CheckerEnv
open LuaChecker.TypeSystem
open LuaChecker.Primitives
open LuaChecker.Syntax
module D = Documents


[<AutoOpen>]
module private Helpers =
    let reportParseErrors env span es =
        for e in es do
            CheckerEnv.reportInfo env span <| DiagnosticKind.ParseError e

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
    | VarType({ target = LuaChecker.Var(_, ({ kind = InterfaceConstraint fs } as c)) } as r) when Constraints.hasField c ->
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
