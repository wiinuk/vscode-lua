namespace LuaChecker
open System.Diagnostics.CodeAnalysis

module Array =
    /// alias of `System.Array.Empty()`
    [<GeneralizableValue>]
    let empty<'T> = System.Array.Empty<'T>()

module Map =
    let tryFind key (map: Map<_,_>) =
        let mutable result = Unchecked.defaultof<_>
        if map.TryGetValue(key, &result)
        then ValueSome result
        else ValueNone

module Seq =
    [<SuppressMessage("UnusedMemberAssemblyAnalyzer", "AA0001:MemberUnused")>]
    let inline tryPickV chooser (xs: #seq<_>) =
        use e = xs.GetEnumerator()
        let mutable result = ValueNone
        while
            if e.MoveNext() then
                match chooser e.Current with
                | ValueSome _ as r -> result <- r; false
                | _ -> true
            else
                false
            do ()
        result

    let sepBy sep (xs: _ seq) = seq {
        use e = xs.GetEnumerator()
        if not <| e.MoveNext() then () else
        yield! e.Current
        while e.MoveNext() do
            yield! sep
            yield! e.Current
    }

module VOption =
    let box = function ValueSome x -> Some x | _ -> None

module Option =
    let unbox = function Some x -> ValueSome x | _ -> ValueNone

module List =
    let rec revAppend rs xs =
        match rs with
        | [] -> xs
        | r::rs -> revAppend rs (r::xs)

    let inline tryRemove predicate xs =
        let mutable consumedRev = []
        let mutable rest = xs
        let mutable result = ValueNone
        while
            match rest with
            | [] -> false
            | x::xs ->
                if predicate x then
                    result <- ValueSome struct(x, revAppend consumedRev xs); false
                else
                    consumedRev <- x::consumedRev
                    rest <- xs
                    true
            do ()
        result

type ResultBuilder = | ResultBuilder with
    member inline _.Return x = Ok x
    member inline _.ReturnFrom x = x
    member inline _.Bind(r, f) =
        match r with
        | Ok x -> f x
        | Error e -> Error e

module Result =
    let inline defaultWith errorChunk = function
        | Ok x -> x
        | Error e -> errorChunk e

    let inline foldSequence folder state xs =
        let mutable list = xs
        let mutable state = state
        let mutable result = Ok state
        while
            match list with
            | [] -> result <- Ok state; false
            | x::xs ->
                match folder state x with
                | Ok s -> state <- s; list <- xs; true
                | Error e -> result <- Error e; false
            do ()
        result

    module Operators =
        let result = ResultBuilder
