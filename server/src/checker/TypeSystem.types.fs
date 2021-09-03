namespace rec LuaChecker
open Cysharp.Text
open LuaChecker.Primitives
open LuaChecker.TypeWriteHelpers
open System.Diagnostics
open System.Runtime.CompilerServices
open System.Runtime.InteropServices
open System.Threading

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
type TypePrintScope<'VarSubst> = {
    visitedVars: VarTypeSite list
    varSubstitutions: VarSubstitutions<'VarSubst>
}
module TypePrintScope =
    let empty varSubstitutions = { visitedVars = []; varSubstitutions = varSubstitutions }

[<Struct>]
type IndexedName = IndexedName of baseName: string * index: uint64

[<Struct>]
type TypePrintState = {
    style: TypePrintOptions
    mutable nameToId: Assoc<IndexedName, TypeParameterId>
    mutable nameToVar: Assoc<IndexedName, VarTypeSite>
}
module TypePrintState =
    let create style = {
        style = style
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
        | VarType({ varKind = IsMultiKind true } as r) -> ValueSome r
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

    let getOrCreateFleshVarName r (state: _ byref) =
        getOrCreateFleshName r (uint64 <| RuntimeHelpers.GetHashCode r) r.varDisplayName &state.nameToVar

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

type Var<'T,'Constraints> =
    | Var of level: int * 'Constraints
    | Assigned of 'T

type IReadOnlySubst<'K,'V> when 'K : comparison =
    abstract TryFind: 'K -> 'V voption
    abstract ToImmutable: unit -> Subst<'K,'V>

module Subst =
    let empty = ImmutableSubst Map.empty

    let create() = { keyToValue = ref Map.empty }
    let tryFind (s: 'Subst when 'Subst :> IReadOnlySubst<_,_> and 'Subst : struct) var = s.TryFind var
    let toImmutable (s: 'Subst when 'Subst :> IReadOnlySubst<_,_> and 'Subst : struct) = s.ToImmutable()

    let rec assign subst k v =
        let location = &subst.keyToValue.contents
        let oldMap = Volatile.Read &location
        let newMap = Map.add k v oldMap
        if not <| LanguagePrimitives.PhysicalEquality oldMap (Interlocked.CompareExchange(&location, newMap, oldMap)) then
            assign subst k v

[<Struct; NoEquality; NoComparison>]
type MutableSubst<'K,'V> when 'K : comparison = private {
    keyToValue: Map<'K,'V> ref
} with
    interface IReadOnlySubst<'K,'V> with
        member x.TryFind k = Map.tryFind k x.keyToValue.contents
        member x.ToImmutable() = ImmutableSubst x.keyToValue.contents

/// immutable
[<Struct>]
type Subst<'K,'V> when 'K : comparison = private ImmutableSubst of Map<'K,'V> with
    interface IReadOnlySubst<'K,'V> with
        member x.TryFind k =
            let (ImmutableSubst xs) = x
            Map.tryFind k xs

        member x.ToImmutable() = x

[<Struct>]
type VarSubstitutions<'VarSubst> = {
    varSubst: 'VarSubst
}
type VarSubstitutions = VarSubstitutions<Subst<VarTypeSite, TypeVar>>
type MutableVarSubstitutions = VarSubstitutions<MutableSubst<VarTypeSite, TypeVar>>

[<CustomEquality; CustomComparison>]
type VarSite<'T,'Constraints,'K> = {
    varDisplayName: string
    varId: int64
    varKind: 'K
    initialTarget: Var<'T,'Constraints>
}
with
    member x.Equals y = x.varId = y.varId
    member x.CompareTo y = x.varId.CompareTo y.varId
    override x.Equals y =
        match y with
        | :? VarSite<'T,'Constraints,'K> as y -> x.Equals y
        | _ -> false

    override x.GetHashCode() = x.varId.GetHashCode()

    interface System.IEquatable<VarSite<'T,'Constraints,'K>> with
        member x.Equals y = x.Equals y

    interface System.IComparable<VarSite<'T,'Constraints,'K>> with
        member x.CompareTo y = x.CompareTo y

    interface System.IComparable with
        member x.CompareTo y = x.CompareTo(y :?> VarSite<'T,'Constraints,'K>)

type VarKindSite = VarSite<Kind, HEmpty, HEmpty>
type VarTypeSite = VarSite<Type, Constraints, Kind>
type TypeVar = Var<Type, Constraints>

module VarSubstitutions =
    let empty: VarSubstitutions = { varSubst = Subst.empty }
    let newEmpty() = { varSubst = Subst.create() }
    let toImmutable c = {
        varSubst = Subst.toImmutable c.varSubst
    }


module Var =
    let private nextId = ref 1L
    let newVarWith displayName level kind c = {
        varId = Interlocked.Increment nextId
        varKind = kind
        varDisplayName = displayName
        initialTarget = Var(level, c)
    }

    let newVar displayName level kind = newVarWith displayName level kind InternalConstraints.any

    let assignTarget substitutions v t =
        Subst.assign substitutions.varSubst v t

    let target substitutions v =
        match Subst.tryFind substitutions.varSubst v with
        | ValueSome t -> t
        | _ -> v.initialTarget

    let (|Target|) substitutions v = target substitutions v

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
        let mutable state = TypePrintState.create options
        let scope = TypePrintScope.empty VarSubstitutions.empty
        KindExtensions.Append(&b, x, &scope, &state)
        b.ToString()

[<Extension>]
type KindExtensions =
    [<Extension>]
    static member Append(b: Utf16ValueStringBuilder byref, k, options: _ inref, state: _ byref) =
        match k with
        | NamedKind name -> b.Append name
        | FunKind([], k) ->
            b.Append "fun()"
            if state.style.enableAllowStyleFunResult
            then b.Append " -> "
            else b.Append ": "
            b.Append(k, &options, &state)

        | FunKind(k::ks, k') ->
            b.Append "fun("
            b.Append(k, &options, &state)
            for k in ks do
                b.Append ", "
                b.Append(k, &options, &state)
            b.Append ")"
            if state.style.enableAllowStyleFunResult
            then b.Append " -> "
            else b.Append ": "
            b.Append(k', &options, &state)

[<Struct; CustomComparison; CustomEquality>]
type TypeParameterId = TypeParameterId of int64 * Kind
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
        let mutable state = TypePrintState.create TypeWriteOptions.Debugger
        let options = { visitedVars = []; varSubstitutions = VarSubstitutions.empty }
        TypeExtensions.Append(&b, x, &options, &state)
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
        let mutable state = TypePrintState.create options
        let scope = TypePrintScope.empty VarSubstitutions.empty
        ConstraintsExtensions.AppendConstraints(&b, x, &scope, &state)
        b.ToString()

module internal InternalConstraints =
    let any = { kind = InterfaceConstraint Map.empty; trivia = [] }
    let isAny c =
        match c.kind with
        | InterfaceConstraint fs -> Map.isEmpty fs
        | _ -> false

[<Extension>]
type ConstraintsExtensions =
    [<Extension>]
    static member AppendConstraints(b: _ byref, c, options: _ inref, state: _ byref) =
        match c with
        | InterfaceConstraint fs -> FieldsExtensions.Append(&b, fs, &options, &state)
        | MultiElementTypeConstraint t -> b.Append(t.kind, &options, &state)
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
        | [t] -> b.Append(t.kind, &options, &state)
        | t::ts ->

        b.Append '('
        b.Append(t.kind, &options, &state)
        for t in ts do
            b.Append " | "
            b.Append(t.kind, &options, &state)
        b.Append ')'

[<Extension>]
type FieldsExtensions =
    [<Extension>]
    static member Append(b: Utf16ValueStringBuilder byref, fields, options: _ inref, state: _ byref) =
        b.Append "{ "
        for kv in fields do
            b.Append(kv.Key); b.Append ": "; TypeExtensions.Append(&b, kv.Value.kind, &options, &state); b.Append "; "
        b.Append '}'

[<Extension>]
type TypeParameterExtensions =
    [<Extension>]
    static member Append(b: Utf16ValueStringBuilder byref, p, options: _ inref, state: _ byref) =
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
type TypeExtensions =
    [<Extension>]
    static member Append(b: _ byref, x, options: _ inref, state: _ byref) =
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
        | InterfaceType fields -> b.Append(fields, &options, &state)
        | ParameterType(TypeParameterId(x, k) as p) ->
            b.AppendIndexedName(getOrCreateFleshParameterName p "TFree" &state)
            if style.showId then
                b.Append '\''; b.Append x
            b.AppendKindMark(k, &options, &state)

        | TypeAbstraction(ps, t) ->
            match ps with
            | [] when not style.showEmptyTypeAbstraction -> b.Append(t.kind, &options, &state)
            | [] ->
                b.Append "type()"
                if style.enableAllowStyleFunResult
                then b.Append " -> "
                else b.Append ": "
                b.Append(t.kind, &options, &state)
            | (p::ps) as pps ->

            for TypeParameter(name, p, _) in pps do
                getOrCreateFleshParameterName p name &state |> ignore

            b.Append "type("
            b.Append(p, &options, &state)
            for p in ps do
                b.Append ", "
                b.Append(p, &options, &state)
            b.Append ")"
            if style.enableAllowStyleFunResult
            then b.Append " -> "
            else b.Append ": "
            b.Append(t.kind, &options, &state)

    [<Extension>]
    static member AppendVarType(b: _ byref, ({ varKind = kind } as r), options: _ inref, state: _ byref) =
        if List.contains r options.visitedVars then
            b.Append "rec "
            b.AppendVarIdAndQ(r, &state)
            b.AppendKindMark(kind, &options, &state)
        else
            let options = { options with visitedVars = r::options.visitedVars }
            match Var.target options.varSubstitutions r with
            | Assigned t ->
                if state.style.showAssign then
                    b.Append "("
                    b.AppendVarIdAndQ(r, &state)
                    b.AppendKindMark(kind, &options, &state)

                    b.Append " := "
                    b.Append(t.kind, &options, &state)
                    b.Append ')'
                else
                    b.Append(t.kind, &options, &state)

            | Var(l, c) ->
                b.AppendVarIdAndQ(r, &state)
                if state.style.showTypeLevel && l <> 0 then
                    b.Append '('
                    b.Append l
                    b.Append ')'
                b.AppendKindMark(kind, &options, &state)

                if not <| InternalConstraints.isAny c then
                    match r.varKind with
                    | IsMultiKind true -> ()
                    | NamedKind _
                    | FunKind _ -> b.Append ": "
                    b.AppendConstraints(c.kind, &options, &state)

    [<Extension>]
    static member AppendVarIdAndQ(b: _ byref, r, state: _ byref) =
        b.Append '?'
        b.AppendIndexedName(getOrCreateFleshVarName r &state)
        if state.style.showId then
            b.Append '\''
            b.Append(RuntimeHelpers.GetHashCode r)

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
                b.Append(kind, &options, &state)

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
                b.Append(t1.kind, &options, &state)
                b.AppendOperatorTail(opName, ts, &options, &state)

    [<Extension>]
    static member AppendNamedTypeApply(b: _ byref, TypeConstant(name, kind), ts, options: _ inref, state: _ byref) =
        b.Append name
        if state.style.showKind then
            b.Append " :: "
            b.Append(kind, &options, &state)

        match ts with
        | [] -> ()
        | t::ts ->
            b.Append '<'; b.Append(t.kind, &options, &state)
            for t in ts do b.Append ", "; b.Append(t.kind, &options, &state)
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
            b.Append(t.kind, &options, &state)
            i <- i + 1

[<Extension>]
type MultiTypeExtensions =
    [<Extension>]
    static member AppendNoWrap(b: _ byref, m, options: _ inref, state: _ byref) =
        match m with
        | IsEmptyType true -> ()
        | ConsType(ValueSome(t, { kind = IsEmptyType true })) -> b.Append(t.kind, &options, &state)
        | ConsType(ValueSome(t1, m)) -> b.Append(t1.kind, &options, &state); b.AppendRest(m.kind, &options, &state)
        | t -> b.Append(t, &options, &state)

    [<Extension>]
    static member AppendRest(b: _ byref, m, options: _ inref, state: _ byref) =
        let rec isEmpty varSubstitutions showAssign = function
            | IsEmptyType true -> true
            | MultiVarType(ValueSome(Var.Target varSubstitutions (Assigned m))) -> if showAssign then false else isEmpty varSubstitutions showAssign m.kind
            | _ -> false

        if not <| isEmpty options.varSubstitutions state.style.showAssign m then b.Append ", "
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
        let rec isSingle varSubstitutions = function
            // m... := m2
            | MultiVarType(ValueSome(Var.Target varSubstitutions (Assigned m))) -> isSingle varSubstitutions m.kind
            // ...et
            | MultiVarType(ValueSome(Var.Target varSubstitutions (Var(_, IsAnyConstraint true))))
            // 'm...
            | MultiParameterType(ValueSome _)
            // (t,)
            | ConsType(ValueSome(_, { kind = IsEmptyType true }))
            // 'm...et
            | MultiVarType(ValueSome(Var.Target varSubstitutions (Var(_, { kind = MultiElementTypeConstraint _ })))) -> true
            // ()
            | IsEmptyType true
            // (t, m)
            | ConsType(ValueSome _) -> false

            // without multi kind
            | _ -> false

        let isSingle = isSingle options.varSubstitutions m
        if not isSingle || not singleElementNoWrap then b.Append '('
        b.AppendNoWrap(m, &options, &state)
        if isSingle && not singleElementNoQuote then b.Append ','
        if not isSingle || not singleElementNoWrap then b.Append ')'

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
