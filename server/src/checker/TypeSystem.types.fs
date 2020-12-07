namespace rec LuaChecker
open Cysharp.Text
open LuaChecker.Primitives
open LuaChecker.TypeWriteHelpers
open System.Diagnostics
open System.Runtime.CompilerServices
open System.Runtime.InteropServices
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

[<ReferenceEquality; NoComparison>]
type VarSite<'T,'Constraints,'K> = {
    mutable target: Var<'T,'Constraints>
    varKind: 'K
    varDisplayName: string
}
type VarKindSite = VarSite<Kind, HEmpty, HEmpty>
type VarTypeSite = VarSite<Type, Constraints, Kind>

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
        let scope = TypePrintScope.empty
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

module VarType =
    let physicalEquality (v1: VarSite<_,_,_>) (v2: VarSite<_,_,_>) =
        LanguagePrimitives.PhysicalEquality v1 v2

[<Struct>]
type TypeConstant = TypeConstant of name: string * Kind

type Type = Token<Type', Location list>
[<DebuggerDisplay "{_DebuggerDisplay,nq}"; StructuredFormatDisplay "{_DebuggerDisplay}">]
type Type' =
    ///<summary>e.g. `number` `table&lt;number, ?v&gt;` `fun(): ()`</summary>
    | NamedType of TypeConstant * Type list
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
        let options = { visitedVars = [] }
        TypeExtensions.Append(&b, x, &options, &state)
        b.ToString()

[<RequireQualifiedAccess>]
type TagElement =
    | Literal of S.LiteralKind
    | AllBoolean
    | AllNumber
    | AllString
    | AllTable
    | AllFunction
    | AllThread

module TagElement =
    let show e =
        let mutable b = ZString.CreateStringBuilder()
        ConstraintsExtensions.AppendTagElement(&b, e)
        b.ToString()

[<System.Flags>]
type TagSet =
    | Empty         = 0b00000000uy
    | Nil           = 0b00000001uy
    | False         = 0b00000010uy
    | True          = 0b00000100uy
    | AllNumber     = 0b00001000uy
    | AllString     = 0b00010000uy
    | AllTable      = 0b00100000uy
    | AllFunction   = 0b01000000uy
    | AllThread     = 0b10000000uy

[<DebuggerDisplay "{_DebuggerDisplay,nq}"; StructuredFormatDisplay "{_DebuggerDisplay}">]
type TagSpace = {
    tagSet: TagSet
    numberElements: double Set
    stringElements: string Set
}
with
    [<DebuggerBrowsable(DebuggerBrowsableState.Never)>]
    member private x._DebuggerDisplay =
        use mutable b = ZString.CreateStringBuilder()
        TagSpaceExtensions.Append(&b, x)
        b.ToString()

    static member (+)(l, r) = TagSpace.union l r

[<Extension>]
type TagSpaceExtensions =
    [<Extension>]
    static member Append(b: _ byref, s) =
        let isSingle = TagSpace.lexicalElementCount s <= 1

        if not isSingle then b.Append '('
        let xs = TagSpace.toElements s

        let emptySymbol = '\u2205' // '∅' ( EMPTY SET )

        match Set.count xs with
        | 0 -> b.Append emptySymbol
        | 1 -> b.AppendTagElement(Set.minElement xs)
        | _ ->
            use e = Set.toSeq(xs).GetEnumerator()
            if e.MoveNext() then
                b.AppendTagElement(e.Current)
                while e.MoveNext() do
                    b.Append " | "
                    b.AppendTagElement(e.Current)
            else
                b.Append emptySymbol

        if not isSingle then b.Append ')'

module TagSpace =
    module private TagSet =
        let [<Literal>] AllBoolean = TagSet.True ||| TagSet.False
        let [<Literal>] Full =
            TagSet.Nil |||
            TagSet.False |||
            TagSet.True |||
            TagSet.AllNumber |||
            TagSet.AllString |||
            TagSet.AllTable |||
            TagSet.AllFunction |||
            TagSet.AllThread

    let private ofTagSet x = {
        tagSet = x
        numberElements = Set.empty
        stringElements = Set.empty
    }

    let empty = ofTagSet TagSet.Empty
    /// nil
    let nil = ofTagSet TagSet.Nil
    /// boolean
    let allBoolean = ofTagSet TagSet.AllBoolean
    /// number
    let allNumber = ofTagSet TagSet.AllNumber
    /// string
    let allString = ofTagSet TagSet.AllString
    /// table
    let allTable = ofTagSet TagSet.AllTable
    /// function
    let allFunction = ofTagSet TagSet.AllFunction
    /// thread
    let allThread = ofTagSet TagSet.AllThread
    let full = ofTagSet TagSet.Full

    let ofLiteral = function
        | S.Nil -> ofTagSet TagSet.Nil
        | S.False -> ofTagSet TagSet.False
        | S.True -> ofTagSet TagSet.True
        | S.Number x -> { tagSet = TagSet.Empty; numberElements = Set.singleton x; stringElements = Set.empty }
        | S.String x -> { tagSet = TagSet.Empty; numberElements = Set.empty; stringElements = Set.singleton x }

    let containsAllBoolean s = s.tagSet &&& TagSet.AllBoolean = TagSet.AllBoolean
    let containsAllNumber s = s.tagSet &&& TagSet.AllNumber = TagSet.AllNumber
    let containsAllString s = s.tagSet &&& TagSet.AllString = TagSet.AllString

    let isEmpty s = s.tagSet = TagSet.Empty && Set.isEmpty s.numberElements && Set.isEmpty s.stringElements
    let isFull s = s.tagSet &&& TagSet.Full = TagSet.Full

    /// isEmpty (s1 - s2)
    let isSubset s1 s2 =
        (s1.tagSet &&& ~~~s2.tagSet = TagSet.Empty) &&
        (containsAllNumber s2 || Set.isSubset s1.numberElements s2.numberElements) &&
        (containsAllString s2 || Set.isSubset s1.stringElements s2.stringElements)

    let private popCount32 x =
        let x = x - ((x >>> 1) &&& 0x55555555u)
        let x = (x &&& 0x33333333u) + ((x >>> 2) &&& 0x33333333u)
        let x = ((x + (x >>> 4)) &&& 0xF0F0F0Fu) * 16843009u >>> 24
        int x

    let lexicalElementCount s =
        Set.count s.numberElements +
        Set.count s.stringElements +
        popCount32(uint32 s.tagSet)

    /// normalize (string | "a" | "b" | 1) = (string | 1)
    let normalize s =
        let s =
            if s.tagSet &&& TagSet.AllNumber = TagSet.AllNumber
            then { s with numberElements = Set.empty }
            else s

        let s =
            if s.tagSet &&& TagSet.AllString = TagSet.AllString
            then { s with stringElements = Set.empty }
            else s
        s

    let union s1 s2 = normalize {
        tagSet = s1.tagSet ||| s2.tagSet
        numberElements = s1.numberElements + s2.numberElements
        stringElements = s1.stringElements + s2.stringElements
    }
    let intersect s1 s2 = normalize {
        tagSet = s1.tagSet &&& s2.tagSet
        numberElements = Set.intersect s1.numberElements s2.numberElements
        stringElements = Set.intersect s1.stringElements s2.stringElements
    }
    let private has s x = s.tagSet &&& x = x
    let toElements s = Set.ofSeq <| seq {
        if has s TagSet.Nil then TagElement.Literal S.Nil
        if containsAllBoolean s
        then
            TagElement.AllBoolean
        else
            if has s TagSet.False then TagElement.Literal S.False
            if has s TagSet.True then TagElement.Literal S.True
        if has s TagSet.AllNumber then TagElement.AllNumber
        if has s TagSet.AllString then TagElement.AllString
        if has s TagSet.AllTable then TagElement.AllTable
        if has s TagSet.AllFunction then TagElement.AllFunction
        if has s TagSet.AllThread then TagElement.AllThread
        for x in s.numberElements do TagElement.Literal <| S.Number x
        for x in s.stringElements do TagElement.Literal <| S.String x
    }

    let difference1 s1 s2 =
        let notContainsNumber xs =
            if not <| Set.contains 0. xs then 0. else

            let x = Set.maxElement xs
            let maxSafeInteger = 9007199254740991.
            if not (System.Double.IsNaN x || System.Double.IsInfinity x || maxSafeInteger <= x) then round x + 1. else

            let x = Set.minElement xs
            let minSafeInteger = -9007199254740991.
            if not (System.Double.IsNaN x || System.Double.IsInfinity x || x <= minSafeInteger) then round x - 1. else

            Seq.initInfinite double |> Seq.find (fun x -> Set.contains x xs |> not)

        let notContainsString xs =
            if not <| Set.contains "a" xs then "a" else
            Seq.initInfinite (fun x ->
                let c = char (int 'a' + x)
                if c <= 'z' then string c
                else sprintf "a%d" <| x - (int 'z' - int 'a')
            )
            |> Seq.find (fun x -> Set.contains x xs |> not)

        let diff1Numbers s1 s2 =
            match containsAllNumber s1, containsAllNumber s2 with

            // diff ( … | number | … ) ( … | number | … )
            // diff ( … | 0 | 1 | 2 | … ) ( … | number | … )
            | _, true -> ValueNone

            // diff ( … | 0 | 1 | 2 | … ) ( … | 0 | 1 | 2 | … )
            | false, _ ->
                let ns = s1.numberElements - s2.numberElements
                if Set.isEmpty ns then ValueNone
                else Set.minElement ns |> S.Number |> TagElement.Literal |> ValueSome

            // diff ( … | number | … ) ( … | 0 | 1 | 2 | … )
            | true, _ ->
                if Set.isEmpty s2.numberElements
                then ValueSome TagElement.AllNumber
                else notContainsNumber s2.numberElements |> S.Number |> TagElement.Literal |> ValueSome

        let diff1Strings s1 s2 =
            match containsAllString s1, containsAllString s2 with
            | _, true -> ValueNone
            | false, _ ->
                let ss = s1.stringElements - s2.stringElements
                if Set.isEmpty ss then ValueNone
                else Set.minElement ss |> S.String |> TagElement.Literal |> ValueSome
            | true, _ ->
                if Set.isEmpty s2.numberElements
                then ValueSome TagElement.AllString
                else notContainsString s2.stringElements |> S.String |> TagElement.Literal |> ValueSome

        match diff1Numbers s1 s2 with
        | ValueSome _ as r -> r
        | _ ->

        match diff1Strings s1 s2 with
        | ValueSome _ as r -> r
        | _ -> ofTagSet (s1.tagSet &&& ~~~s2.tagSet) |> toElements |> Seq.tryHead |> Option.unbox

    let show s =
        let mutable b = ZString.CreateStringBuilder()
        TagSpaceExtensions.Append(&b, s)
        b.ToString()

type Constraints = Token<Constraints', Location list>
[<DebuggerDisplay "{_DebuggerDisplay,nq}"; StructuredFormatDisplay "{_DebuggerDisplay}">]
type Constraints' =
    /// empty = any
    | InterfaceConstraint of Map<FieldKey, Type>
    | MultiElementTypeConstraint of Type
    /// e.g. `'a : (10 | "a" | table)..` `'a : ..number`
    | TagSpaceConstraint of lowerBound: TagSpace * upperBound: TagSpace
with
    [<DebuggerBrowsable(DebuggerBrowsableState.Never)>]
    member private x._DebuggerDisplay =
        use mutable b = ZString.CreateStringBuilder()
        let options = TypeWriteOptions.Debugger
        let mutable state = TypePrintState.create options
        let scope = TypePrintScope.empty
        ConstraintsExtensions.AppendConstraints(&b, x, &scope, &state)
        b.ToString()

module internal InternalConstraints =
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
        | TagSpaceConstraint(lower, upper) ->
            if lower = upper then b.Append(lower) else

            if not <| TagSpace.isEmpty lower then
                b.Append(lower)
            b.Append ".."
            if not <| TagSpace.isFull upper then
                b.Append(upper)

    [<Extension>]
    static member AppendTagElement(b: _ byref, x) =
        match x with
        | TagElement.Literal x -> b.AppendLiteral x
        | TagElement.AllBoolean -> b.Append "boolean"
        | TagElement.AllNumber -> b.Append "number"
        | TagElement.AllString -> b.Append "string"
        | TagElement.AllTable -> b.Append "table"
        | TagElement.AllFunction -> b.Append "function"
        | TagElement.AllThread -> b.Append "thread"

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
        if List.exists (VarType.physicalEquality r) options.visitedVars then
            b.Append "rec "
            b.AppendVarIdAndQ(r, &state)
            b.AppendKindMark(kind, &options, &state)
        else
            let options = { options with visitedVars = r::options.visitedVars }
            match r.target with
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
        let rec isEmpty showAssign = function
            | IsEmptyType true -> true
            | MultiVarType(ValueSome { target = Assigned m }) -> if showAssign then false else isEmpty showAssign m.kind
            | _ -> false

        if not <| isEmpty state.style.showAssign m then b.Append ", "
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
        let rec isSingle = function
            // m... := m2
            | MultiVarType(ValueSome { target = Assigned m }) -> isSingle m.kind
            // ...et
            | MultiVarType(ValueSome { target = Var(_, IsAnyConstraint true) })
            // 'm...
            | MultiParameterType(ValueSome _)
            // (t,)
            | ConsType(ValueSome(_, { kind = IsEmptyType true }))
            // 'm...et
            | MultiVarType(ValueSome { target = Var(_, { kind = MultiElementTypeConstraint _ }) }) -> true
            // ()
            | IsEmptyType true
            // (t, m)
            | ConsType(ValueSome _) -> false

            // without multi kind
            | _ -> false

        let isSingle = isSingle m
        if not isSingle || not singleElementNoWrap then b.Append '('
        b.AppendNoWrap(m, &options, &state)
        if isSingle && not singleElementNoQuote then b.Append ','
        if not isSingle || not singleElementNoWrap then b.Append ')'

type Scheme = Type

type TypeSystem = {
    nilConstant: TypeConstant
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
