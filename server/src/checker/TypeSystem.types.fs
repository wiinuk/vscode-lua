namespace rec LuaChecker
open Cysharp.Text
open LuaChecker.Primitives
open LuaChecker.TypeWriteHelpers
open System.Diagnostics
open System.Runtime.CompilerServices
open System.Runtime.InteropServices
open System.Collections.Concurrent
open Cysharp.Text
open Cysharp.Text

module Name = Syntax.Name
module S = Syntaxes


type Assoc<'k,'v> = (struct('k * 'v)) list
module Assoc =
    let empty = []
    let add k v kvs = struct(k, v)::kvs
    let remove k = function
        | [] -> []
        | struct(k',_)::kvs when k = k' -> remove k kvs
        | kv::kvs -> kv::remove k kvs

    let inline tryFindBy eq k kvs =
        let mutable remaining = kvs
        let mutable result = ValueNone
        while
            match remaining with
            | [] -> false
            | struct(k',v')::kvs ->
                if eq k k' then
                    result <- ValueSome v'
                    false
                else
                    remaining <- kvs
                    true
            do ()
        result

    let tryFind k kvs = tryFindBy (=) k kvs

    let inline tryFindKeyBy eq v kvs =
        let mutable remaining = kvs
        let mutable result = ValueNone
        while
            match remaining with
            | [] -> false
            | struct(k',v')::kvs ->
                if eq v v' then
                    result <- ValueSome k'
                    false
                else
                    remaining <- kvs
                    true
            do ()
        result

    let tryFindKey v kvs = tryFindKeyBy (=) v kvs

type TypePrintOptions = {
    showAssign: bool
    showTypeLevel: bool
    showMultiVarName: bool
    showEmptyTypeAbstraction: bool
    disableTypeOperator: bool
    showKind: bool
    enableAllowStyleFunResult: bool
    showId: bool
}
[<Struct>]
type TypePrintScope = {
    visitedVars: VarTypeSite list
}
module TypePrintScope =
    let empty = { visitedVars = [] }

[<Struct>]
type IndexedName = IndexedName of baseName: string * index: uint64

type IReadonlySubst<'Right> =
    abstract TryFind: Var<'K,'C> -> 'Right voption
    abstract ToImmutable: unit -> 'Right Subst

module Subst =
    open System.Threading

    let empty = ImmutableSubst Map.empty

    let create() = { variableIdToRight = ref Map.empty }
    let createOfSeq assigns =
        let subst = create()
        for v, r in assigns do
            assign subst v r
        subst

    let tryFind (s: 'Subst when 'Subst :> IReadonlySubst<'R> and 'Subst : struct) var = s.TryFind var
    let toImmutable (s: 'Subst when 'Subst :> IReadonlySubst<'R> and 'Subst : struct) = s.ToImmutable()

    let (|Find|) s v =
        match tryFind s v with
        | ValueSome x -> Ok x
        | _ -> Error v

    let rec assign subst (Var(id = id) as var) right =
        let location = &subst.variableIdToRight.contents
        let oldMap = Volatile.Read &location
        let newMap = Map.add id right oldMap
        if not <| LanguagePrimitives.PhysicalEquality oldMap (Interlocked.CompareExchange(&location, newMap, oldMap)) then
            assign subst var right

[<Struct; NoEquality; NoComparison>]
type MutableSubst<'Right> = private {
    variableIdToRight: Map<int64,'Right> ref
} with
    interface IReadonlySubst<'Right> with
        member x.TryFind (Var(id = id)) =
            Map.tryFind id x.variableIdToRight.contents

        member x.ToImmutable() = ImmutableSubst x.variableIdToRight.contents

/// immutable
[<Struct; NoEquality; NoComparison>]
type Subst<'Right> = private ImmutableSubst of variableIdToRight: Map<int64,'Right> with
    interface IReadonlySubst<'Right> with
        member x.TryFind (Var(id = id)) =
            let (ImmutableSubst xs) = x
            Map.tryFind id xs

        member x.ToImmutable() = x

[<Struct>]
type TypePrintState<'Subst> = {
    style: TypePrintOptions
    subst: 'Subst
    mutable nameToId: Assoc<IndexedName, TypeParameterId>
    mutable nameToVar: Assoc<IndexedName, VarTypeSite>
}
module TypePrintState =
    let create subst style = {
        style = style
        subst = subst
        nameToId = Assoc.empty
        nameToVar = Assoc.empty
    }

module private TypeWriteHelpers =
    let (|IsAnyConstraint|) c = InternalConstraints.isAny c
    let (|IsValueKind|) = function NamedKind "value" -> true | _ -> false
    let (|IsMultiKind|) = function NamedKind "multi" -> true | _ -> false

    let (|IsEmptyType|) = function
        | NamedType(TypeConstant("()", IsMultiKind true), []) -> true
        | _ -> false

    let (|ConsType|) = function
        | NamedType(TypeConstant("(::)", FunKind([IsValueKind true; IsMultiKind true], IsMultiKind true)), [t1; t2]) -> ValueSome struct(t1, t2)
        | _ -> ValueNone

    let (|MultiVarType|) = function
        | VarType(Var(kind = IsMultiKind true) as r) -> ValueSome r
        | _ -> ValueNone

    let (|MultiParameterType|) = function
        | ParameterType(TypeParameterId(x, IsMultiKind true)) -> ValueSome x
        | _ -> ValueNone

    let toValidTypeName = function
        | null
        | "" -> "x"

        // TODO: escape
        | x -> x

    let fleshName baseName id nameToId =
        let name = IndexedName(toValidTypeName baseName, 0UL)
        match Assoc.tryFind name nameToId with
        | ValueNone -> name
        | _ ->

        let name = IndexedName(baseName, id)
        match Assoc.tryFind name nameToId with
        | ValueNone -> name
        | _ ->

        let mutable i = 2UL
        let mutable name = baseName
        while
            begin
                match Assoc.tryFind (IndexedName(name, i)) nameToId with
                | ValueNone -> false
                | _ -> true
            end do i <- i + 1UL
        IndexedName(name, i)

    let getOrCreateFleshName v id baseName (assoc: _ byref) =
        match Assoc.tryFindKey v assoc with
        | ValueSome name -> name
        | _ ->

        let fleshName = fleshName baseName id assoc
        assoc <- Assoc.add fleshName v assoc
        fleshName

    let getOrCreateFleshParameterName (TypeParameterId(id, _) as p) baseName (state: _ byref) =
        getOrCreateFleshName p (uint64 id) baseName &state.nameToId

    let getOrCreateFleshVarName (Var(id = id; displayName = n) as r) (state: _ byref) =
        getOrCreateFleshName r (uint64 id) n &state.nameToVar

module TypeWriteOptions =
    let Default = {
        showAssign = false
        showTypeLevel = false
        showMultiVarName = false
        showEmptyTypeAbstraction = false
        disableTypeOperator = false
        showKind = false
        enableAllowStyleFunResult = false
        showId = false
    }
    let Debugger = {
        showAssign = true
        showTypeLevel = true
        showMultiVarName = true
        showEmptyTypeAbstraction = true
        disableTypeOperator = false
        showKind = false
        enableAllowStyleFunResult = true
        showId = true
    }

[<CustomEquality; CustomComparison>]
type Var<'Kind,'Constraints> =
    | Var of
        id: int64 *

        // 代入がある場合無視する
        displayName: string *
        level: int *
        kind: 'Kind *
        constraints: 'Constraints

with
    member x.Equals(Var(id = y)) =
        let (Var(id = x)) = x
        x.Equals y

    member x.CompareTo(Var(id = y)) =
        let (Var(id = x)) = x
        x.CompareTo y

    override x.Equals y =
        match y with
        | :? Var<'Kind,'Constraints> as y -> x.Equals y
        | _ -> false

    override x.GetHashCode() =
        let (Var(id = x)) = x
        x.GetHashCode()

    interface System.IEquatable<Var<'Kind,'Constraints>> with
        member x.Equals y = x.Equals y

    interface System.IComparable<Var<'Kind,'Constraints>> with
        member x.CompareTo y = x.CompareTo y

    interface System.IComparable with
        member x.CompareTo y = x.CompareTo(y :?> Var<'Kind,'Constraints>)

type VarKindSite = Var<HEmpty, HEmpty>
type VarTypeSite = Var<Kind, Constraints>

[<Extension>]
type KindExtensions =
    [<Extension>]
    static member AppendKind(b: Utf16ValueStringBuilder byref, k, options: _ inref, state: _ byref) =
        match k with
        | NamedKind name -> b.Append name
        | FunKind([], k) ->
            b.Append "fun()"
            if state.style.enableAllowStyleFunResult
            then b.Append " -> "
            else b.Append ": "
            b.AppendKind(k, &options, &state)

        | FunKind(k::ks, k') ->
            b.Append "fun("
            b.AppendKind(k, &options, &state)
            for k in ks do
                b.Append ", "
                b.AppendKind(k, &options, &state)
            b.Append ")"
            if state.style.enableAllowStyleFunResult
            then b.Append " -> "
            else b.Append ": "
            b.AppendKind(k', &options, &state)

[<Extension>]
type TypeExtensions =
    [<Extension>]
    static member AppendType(b: Utf16ValueStringBuilder byref, x, options: _ inref, state: _ byref) =
        let style = state.style
        match x with
        | VarType r -> b.AppendVarType(r, &options, &state)
        | NamedType(TypeConstant(_, (NamedKind "multi" | FunKind(_, NamedKind "multi"))), _) ->
            b.AppendMulti(x, &options, &state)

        | NamedType(TypeConstant("(fun)", _), [m1; m2]) ->
            b.Append "fun"
            b.AppendMulti(m1.kind, &options, &state, singleElementNoQuote = true)
            if style.enableAllowStyleFunResult
            then b.Append " -> "
            else b.Append ": "
            b.AppendMulti(m2.kind, &options, &state, singleElementNoWrap = true, singleElementNoQuote = true)

        | NamedType(TypeConstant(name, _) as t, ts) ->
            if style.disableTypeOperator || Name.isValid name
            then b.AppendNamedTypeApply(t, ts, &options, &state)
            else b.AppendOperandTypeApplyOrNamedTypeApply(t, ts, &options, &state)

        | LiteralType x -> b.AppendLiteral x
        | InterfaceType fields -> b.AppendFields(fields, &options, &state)
        | ParameterType(TypeParameterId(x, k) as p) ->
            b.AppendIndexedName(getOrCreateFleshParameterName p "TFree" &state)
            if style.showId then
                b.Append '\''; b.Append x
            b.AppendKindMark(k, &options, &state)

        | TypeAbstraction(ps, t) ->
            match ps with
            | [] when not style.showEmptyTypeAbstraction -> b.AppendType(t.kind, &options, &state)
            | [] ->
                b.Append "type()"
                if style.enableAllowStyleFunResult
                then b.Append " -> "
                else b.Append ": "
                b.AppendType(t.kind, &options, &state)
            | (p::ps) as pps ->

            for TypeParameter(name, p, _) in pps do
                getOrCreateFleshParameterName p name &state |> ignore

            b.Append "type("
            b.AppendTypeParameter(p, &options, &state)
            for p in ps do
                b.Append ", "
                b.AppendTypeParameter(p, &options, &state)
            b.Append ")"
            if style.enableAllowStyleFunResult
            then b.Append " -> "
            else b.Append ": "
            b.AppendType(t.kind, &options, &state)

    [<Extension>]
    static member AppendVarType(b: _ byref, (Var(kind = kind) as r), options: _ inref, state: _ byref) =
        if List.exists ((=) r) options.visitedVars then
            b.Append "rec "
            b.AppendVarIdAndQ(r, &state)
            b.AppendKindMark(kind, &options, &state)
        else
            let options = { options with visitedVars = r::options.visitedVars }
            match Subst.tryFind state.subst r with
            | ValueSome t ->
                if state.style.showAssign then
                    b.Append "("
                    b.AppendVarIdAndQ(r, &state)
                    b.AppendKindMark(kind, &options, &state)

                    b.Append " := "
                    b.AppendType(t.kind, &options, &state)
                    b.Append ')'
                else
                    b.AppendType(t.kind, &options, &state)

            | ValueNone ->
                let (Var(level = l; constraints = c)) = r

                b.AppendVarIdAndQ(r, &state)
                if state.style.showTypeLevel && l <> 0 then
                    b.Append '('
                    b.Append l
                    b.Append ')'
                b.AppendKindMark(kind, &options, &state)

                if not <| InternalConstraints.isAny c then
                    let (Var(kind = k)) = r

                    match k with
                    | IsMultiKind true -> ()
                    | NamedKind _
                    | FunKind _ -> b.Append ": "
                    b.AppendConstraints(c.kind, &options, &state)

    [<Extension>]
    static member AppendVarIdAndQ(b: _ byref, (Var(id = id) as r), state: _ byref) =
        b.Append '?'
        b.AppendIndexedName(getOrCreateFleshVarName r &state)
        if state.style.showId then
            b.Append '\''
            b.Append(uint64 id)

    [<Extension>]
    static member AppendLiteral(b: _ byref, x) =
        match x with
        | S.Nil -> b.Append "nil"
        | S.True -> b.Append "true"
        | S.False -> b.Append "false"
        | S.Number x -> b.AppendNumberLiteral x
        | S.String x -> b.AppendStringLiteral x

    [<Extension>]
    static member AppendNumberLiteral(b: _ byref, x) =
        if System.Double.IsNaN x then b.Append "(0/0)" else
        if System.Double.IsPositiveInfinity x then b.Append "(1/0)" else
        if System.Double.IsNegativeInfinity x then b.Append "(-1/0)" else
        b.Append(x, "G17")

    [<Extension>]
    static member AppendStringLiteral(b: _ byref, x) =
        match x with
        | null -> b.Append "nil"
        | x ->
            for x in Syntax.Printer.showString Syntax.Printer.PrintConfig.defaultConfig x do
                b.Append x

    /// "..." or ": kind" or ""
    [<Extension>]
    static member AppendKindMark(b: _ byref, kind, options: _ inref, state: _ byref) =
        match kind with
        | IsMultiKind true -> b.Append "..."
        | _ ->
            if state.style.showKind then
                b.Append " :: "
                b.AppendKind(kind, &options, &state)

    [<Extension>]
    static member AppendOperandTypeApplyOrNamedTypeApply(b: _ byref, (TypeConstant(name, _) as t), ts, options: _ inref, state: _ byref) =
        match name with
        | null
        | "" -> b.AppendNamedTypeApply(t, ts, &options, &state)

        // "((->): fun(value, value): value)<number, number>"
        | _ when state.style.showKind ->
            b.AppendNamedTypeApply(t, ts, &options, &state)

        | _ ->

        let opName = System.MemoryExtensions.AsSpan name
        let opName =
            if 2 <= opName.Length && opName.[0] = '(' && opName.[name.Length - 1] = ')'
            then opName.Slice(1, opName.Length - 2)
            else opName

        match ts with

        // "()" "(->)"
        | [] -> b.Append name

        // "t1 ? t2 : t3", "t1 * t2 * t3"
        | t1::ts ->
            let separatorCount = List.length ts
            if opName.Length % separatorCount <> 0 then
                b.AppendNamedTypeApply(t, t1::ts, &options, &state)
            else
                b.AppendType(t1.kind, &options, &state)
                b.AppendOperatorTail(opName, ts, &options, &state)

    [<Extension>]
    static member AppendNamedTypeApply(b: _ byref, TypeConstant(name, kind), ts, options: _ inref, state: _ byref) =
        b.Append name
        if state.style.showKind then
            b.Append " :: "
            b.AppendKind(kind, &options, &state)

        match ts with
        | [] -> ()
        | t::ts ->
            b.Append '<'; b.AppendType(t.kind, &options, &state)
            for t in ts do b.Append ", "; b.AppendType(t.kind, &options, &state)
            b.Append '>'

    [<Extension>]
    static member AppendOperatorTail(b: _ byref, opName, ts, options: _ inref, state: _ byref) =
        let separatorCount = List.length ts
        let separatorLength = opName.Length / separatorCount
        let mutable i = 0
        for t in ts do
            b.Append ' '
            b.Append(opName.Slice(i * separatorLength, separatorLength))
            b.Append ' '
            b.AppendType(t.kind, &options, &state)
            i <- i + 1

[<Extension>]
type ConstraintsExtensions =
    [<Extension>]
    static member AppendConstraints(b: _ byref, c, options: _ inref, state: _ byref) =
        match c with
        | InterfaceConstraint fs -> b.AppendFields(fs, &options, &state)
        | MultiElementTypeConstraint t -> b.AppendType(t.kind, &options, &state)
        | UnionConstraint(lower, upper) ->
            if not <| TypeSet.isEmpty lower then
                b.AppendTypeSet(lower, &options, &state)
            b.Append ".."
            if not <| TypeSet.isUniversal upper then
                b.AppendTypeSet(upper, &options, &state)

    [<Extension>]
    static member AppendTypeSet(b: _ byref, typeSet, options: _ inref, state: _ byref) =
        match typeSet with
        | UniversalTypeSet -> b.Append "unknown"
        | TypeSet ts ->

        match ts with
        | [] -> b.Append "never"
        | [t] -> b.AppendType(t.kind, &options, &state)
        | t::ts ->

        b.Append '('
        b.AppendType(t.kind, &options, &state)
        for t in ts do
            b.Append " | "
            b.AppendType(t.kind, &options, &state)
        b.Append ')'

[<Extension>]
type FieldsExtensions =
    [<Extension>]
    static member AppendFields(b: Utf16ValueStringBuilder byref, fields, options: _ inref, state: _ byref) =
        b.Append "{ "
        for kv in fields do
            b.Append(kv.Key); b.Append ": "; b.AppendType(kv.Value.kind, &options, &state); b.Append "; "
        b.Append '}'

[<Extension>]
type TypeParameterExtensions =
    [<Extension>]
    static member AppendTypeParameter(b: Utf16ValueStringBuilder byref, p, options: _ inref, state: _ byref) =
        let (TypeParameter(n, (TypeParameterId(id, kind) as p), c)) = p

        b.AppendIndexedName(getOrCreateFleshParameterName p n &state)
        if state.style.showId then
            b.Append '\''
            b.Append id

        match kind with
        | IsMultiKind true ->
            b.Append "..."
            if not <| InternalConstraints.isAny c then
                b.AppendConstraints(c.kind, &options, &state)

        | NamedKind _
        | FunKind _ ->
            if not <| InternalConstraints.isAny c then
                b.Append ": "
                b.AppendConstraints(c.kind, &options, &state)

    [<Extension>]
    static member AppendIndexedName(b: _ byref, IndexedName(baseName, i)) =
        b.Append baseName
        match i with
        | 0UL -> ()
        | _ -> b.Append i

[<Extension>]
type MultiTypeExtensions =
    [<Extension>]
    static member AppendNoWrap(b: _ byref, m, options: _ inref, state: _ byref) =
        match m with
        | IsEmptyType true -> ()
        | ConsType(ValueSome(t, { kind = IsEmptyType true })) -> b.AppendType(t.kind, &options, &state)
        | ConsType(ValueSome(t1, m)) -> b.AppendType(t1.kind, &options, &state); b.AppendRest(m.kind, &options, &state)
        | t -> b.AppendType(t, &options, &state)

    [<Extension>]
    static member AppendRest(b: _ byref, m, options: _ inref, state: _ byref) =
        let rec isEmpty showAssign subst = function
            | IsEmptyType true -> true
            | MultiVarType(ValueSome(Subst.Find subst (Ok m))) -> if showAssign then false else isEmpty showAssign subst m.kind
            | _ -> false

        if not <| isEmpty state.style.showAssign state.subst m then b.Append ", "
        b.AppendNoWrap(m, &options, &state)

    [<Extension>]
    static member AppendMulti
        (
        b: _ byref, m,
        options: _ inref,
        state: _ byref,
        [<Optional; DefaultParameterValue(false)>] singleElementNoWrap: bool,
        [<Optional; DefaultParameterValue(false)>] singleElementNoQuote: bool
        ) =
        let rec isSingle subst = function
            // m... := m2
            | MultiVarType(ValueSome(Subst.Find subst (Ok m))) -> isSingle subst m.kind
            // ...et
            | MultiVarType(ValueSome(Subst.Find subst (Error(Var(constraints = IsAnyConstraint true)))))
            // 'm...
            | MultiParameterType(ValueSome _)
            // (t,)
            | ConsType(ValueSome(_, { kind = IsEmptyType true }))
            // 'm...et
            | MultiVarType(ValueSome(Subst.Find subst (Error(Var(constraints = { kind = MultiElementTypeConstraint _ }))))) -> true
            // ()
            | IsEmptyType true
            // (t, m)
            | ConsType(ValueSome _) -> false

            // without multi kind
            | _ -> false

        let isSingle = isSingle state.subst m
        if not isSingle || not singleElementNoWrap then b.Append '('
        b.AppendNoWrap(m, &options, &state)
        if isSingle && not singleElementNoQuote then b.Append ','
        if not isSingle || not singleElementNoWrap then b.Append ')'

[<DebuggerDisplay "{_DebuggerDisplay,nq}"; StructuredFormatDisplay "{_DebuggerDisplay}">]
type Kind =
    /// `nil: value`
    /// `string[]: value`
    /// `(fun(): ()): value`
    /// `(): multi`
    /// `(number, string): multi`
    | NamedKind of string
    /// `table: fun(value, value): value`
    /// `thread: fun(multi, multi): multi`
    /// `(::): fun(value, multi): multi`
    | FunKind of Kind list * Kind
with
    [<DebuggerBrowsable(DebuggerBrowsableState.Never)>]
    member private x._DebuggerDisplay =
        use mutable b = ZString.CreateStringBuilder()
        let options = TypeWriteOptions.Debugger
        let mutable state = TypePrintState.create Subst.empty options
        let scope = TypePrintScope.empty
        b.AppendKind(x, &scope, &state)
        b.ToString()

[<Struct; CustomComparison; CustomEquality>]
type TypeParameterId = TypeParameterId of id: int64 * kind: Kind
with
    member x.Equals(TypeParameterId(y, _)) =
        let (TypeParameterId(x, _)) = x
        x.Equals y

    member x.CompareTo(TypeParameterId(y, _)) =
        let (TypeParameterId(x, _)) = x
        x.CompareTo y

    override x.Equals y =
        match y with
        | :? TypeParameterId as y -> x.Equals y
        | _ -> false

    override x.GetHashCode() =
        let (TypeParameterId(x, _)) = x
        x.GetHashCode()

    interface System.IEquatable<TypeParameterId> with
        member x.Equals y = x.Equals y

    interface System.IComparable<TypeParameterId> with
        member x.CompareTo y = x.CompareTo y

    interface System.IComparable with
        member x.CompareTo y = x.CompareTo(y :?> TypeParameterId)

type TypeParameter = TypeParameter of displayName: string * TypeParameterId * Constraints

[<Struct>]
type TypeConstant = TypeConstant of name: string * Kind

type Type = Token<Type', Location list>
[<DebuggerDisplay "{_DebuggerDisplay,nq}"; StructuredFormatDisplay "{_DebuggerDisplay}">]
type Type' =
    ///<summary>e.g. `number` `table&lt;number, ?v&gt;` `fun(): ()`</summary>
    | NamedType of TypeConstant * Type list
    /// e.g. `nil` `false` `-0.5` `"text"`
    | LiteralType of S.LiteralKind
    /// e.g. `{ x: number }`
    | InterfaceType of fields: Map<FieldKey, Type>

    /// e.g. `?a` `?p : { x: number }`
    | VarType of VarTypeSite
    /// e.g. `'a` `'0`
    | ParameterType of TypeParameterId
    /// e.g. `type(a, m...) -> t` `type() -> t`
    | TypeAbstraction of TypeParameter list * Type
with
    [<DebuggerBrowsable(DebuggerBrowsableState.Never)>]
    member private x._DebuggerDisplay =
        use mutable b = ZString.CreateStringBuilder()
        let mutable state = TypePrintState.create Subst.empty TypeWriteOptions.Debugger
        let options = { visitedVars = [] }
        b.AppendType(x, &options, &state)
        b.ToString()

[<Struct>]
type TypeSet =
    | TypeSet of Type list
    | UniversalTypeSet

module TypeSet =
    let empty = TypeSet []
    let isEmpty = function
        | TypeSet [] -> true
        | _ -> false

    let isUniversal = function
        | UniversalTypeSet -> true
        | _ -> false

    let toList = function
        | UniversalTypeSet -> []
        | TypeSet ts -> ts

    let map mapping = function
        | UniversalTypeSet
        | TypeSet [] as t -> t
        | TypeSet ts -> List.map mapping ts |> TypeSet

type Constraints = Token<Constraints', Location list>
[<DebuggerDisplay "{_DebuggerDisplay,nq}"; StructuredFormatDisplay "{_DebuggerDisplay}">]
type Constraints' =
    /// empty = any
    | InterfaceConstraint of Map<FieldKey, Type>
    | MultiElementTypeConstraint of Type
    /// e.g. `'a : (10 | "a" | table)..` `'a : ..number`
    | UnionConstraint of lowerBound: TypeSet * upperBound: TypeSet
with
    [<DebuggerBrowsable(DebuggerBrowsableState.Never)>]
    member private x._DebuggerDisplay =
        use mutable b = ZString.CreateStringBuilder()
        let options = TypeWriteOptions.Debugger
        let mutable state = TypePrintState.create Subst.empty options
        let scope = TypePrintScope.empty
        b.AppendConstraints(x, &scope, &state)
        b.ToString()

module internal InternalConstraints =
    let isAny c =
        match c.kind with
        | InterfaceConstraint fs -> Map.isEmpty fs
        | _ -> false

type Scheme = Type

type TypeSystem = {
    /// `nil`
    nil: Type'
    booleanConstant: TypeConstant
    /// `boolean`
    boolean: Type'
    numberConstant: TypeConstant
    /// `number`
    number: Type'
    stringConstant: TypeConstant
    /// `string`
    string: Type'
    literal: struct(S.LiteralKind * Location list) -> Type

    /// `table :: fun(value, value): value`
    tableConstant: TypeConstant
    ///<summary>`table&lt;k, v&gt;`</summary>
    table: struct(Type * Type) -> Type'
    ///<summary>`table&lt;k, v&gt;`</summary>
    unTable: Type' -> struct(Type * Type) voption

    /// `thread :: fun(multi, multi): value`
    threadConstant: TypeConstant
    ///<summary>`thread&lt;TInput..., TOutput...&gt;`</summary>
    thread: struct(Type * Type) -> Type'
    ///<summary>`thread&lt;TInput..., TOutput...&gt;`</summary>
    unThread: Type' -> struct(Type * Type) voption

    /// `(fun) :: fun(multi, multi): value`
    fnConstant: TypeConstant
    /// `fun(m1): m2`
    fn: struct(Type * Type) -> Type'
    /// `fun(m1): m2`
    unFn: Type' -> struct(Type * Type) voption

    emptyConstant: TypeConstant
    /// `()`
    empty: Type'

    /// `(::)`
    cons: struct(Type * Type) -> Type'
    /// `(::)`
    unCons: Type' -> struct(Type * Type) voption

    /// `value`
    valueKind: Kind
    /// `multi`
    multiKind: Kind
}
