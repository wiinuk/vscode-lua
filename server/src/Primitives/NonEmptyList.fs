namespace LuaChecker.Primitives
open System
open System.Collections.Generic
open System.Diagnostics.CodeAnalysis


[<Struct; NoEquality; NoComparison; RequireQualifiedAccess>]
type NonEmptyListEnumerator<'T> = private {
    mutable state: byte
    mutable current: 'T
    mutable list: 'T list
}
with
    member e.Current = e.current
    member e.MoveNext() =
        match e.state with
        | 0uy -> e.state <- 1uy; true
        | 1uy ->
            match e.list with
            | x::xs ->
                e.current <- x
                e.list <- xs
                true
            | _ ->
                e.state <- 2uy
                false
        | _ -> false

    interface IEnumerator<'T> with
        member e.Current = e.Current
        member e.Current = e.Current :> obj
        member e.MoveNext() = e.MoveNext()
        member _.Reset() = raise <| NotImplementedException()
        member _.Dispose() = ()

[<Struct>]
type NonEmptyList<'T> = NonEmptyList of 'T * 'T list with
    member x.GetEnumerator() =
        let (NonEmptyList(x, xs)) = x
        {
            NonEmptyListEnumerator.state = 0uy
            NonEmptyListEnumerator.current = x
            NonEmptyListEnumerator.list = xs
        }
    interface IEnumerable<'T> with
        member x.GetEnumerator() = x.GetEnumerator() :> _ IEnumerator
        member x.GetEnumerator() = x.GetEnumerator() :> Collections.IEnumerator

module NonEmptyList =
    [<SuppressMessage("UnusedMemberAssemblyAnalyzer", "AA0001:MemberUnused")>]
    let head (NonEmptyList(x, _)) = x
    [<SuppressMessage("UnusedMemberAssemblyAnalyzer", "AA0001:MemberUnused")>]
    let inline map f (NonEmptyList(x, xs)) =
        let x = f x
        match xs with
        | [] -> NonEmptyList(x, [])
        | _ -> NonEmptyList(x, List.map f xs)

    let toList (NonEmptyList(x, xs)) = x::xs
    let singleton x = NonEmptyList(x, [])
    let tryOfList = function [] -> ValueNone | x::xs -> ValueSome(NonEmptyList(x, xs))
    let cons head (NonEmptyList(x, xs)) = NonEmptyList(head, x::xs)
    let rec appendList xs nel =
        match xs with
        | [] -> nel
        | [x] -> cons x nel
        | x::xs -> cons x (appendList xs nel)

    let append (NonEmptyList(x1, xs1)) (NonEmptyList(x2, xs2)) =
        match xs1, xs2 with
        | [], [] -> NonEmptyList(x1, [x2])
        | _ -> NonEmptyList(x1, xs1@x2::xs2)

    [<SuppressMessage("UnusedMemberAssemblyAnalyzer", "AA0001:MemberUnused")>]
    let inline fold folder state (NonEmptyList(x, xs)) =
        let s = folder state x
        match xs with
        | [] -> s
        | _ -> List.fold folder s xs

    [<SuppressMessage("UnusedMemberAssemblyAnalyzer", "AA0001:MemberUnused")>]
    let inline foldBack folder (NonEmptyList(x, xs)) state =
        let state =
            match xs with
            | [] -> state
            | _ -> List.foldBack folder xs state
        folder x state

    [<SuppressMessage("UnusedMemberAssemblyAnalyzer", "AA0001:MemberUnused")>]
    let inline mapFold folder state (NonEmptyList(x, xs)) =
        let struct(x, state) = folder state x
        match xs with
        | [] -> struct(NonEmptyList(x, []), state)
        | _ ->
            let xs, state = List.mapFold (fun state x -> let struct(x, state) = folder state x in x, state) state xs
            NonEmptyList(x, xs), state

    [<SuppressMessage("UnusedMemberAssemblyAnalyzer", "AA0001:MemberUnused")>]
    let inline forall predicate (NonEmptyList(x, xs)) =
        predicate x && List.forall predicate xs
