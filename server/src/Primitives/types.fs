namespace LuaChecker.Primitives
open System.Collections.Concurrent


[<Struct>]
type Scope<'S> = private | Scope

/// local mutable reference
type Local<'S,'T> = private {
    mutable _contents: 'T
}
with
    member x.Value
        with get() = x._contents
        and set(v) = x._contents <- v

type ILocalScope<'R> =
    abstract Invoke: Scope<'S> -> 'R

module Local =
    let get x = x._contents
    let set x v = x._contents <- v
    let create (_: Scope<'S>) (x: 'T): Local<'S,'T> = { _contents = x }
    let inline modify f x = set x (f (get x))

    let run (scope: 'Scope byref when 'Scope :> ILocalScope<_> and 'Scope : struct) = scope.Invoke Scope
    let runNotStruct (scope: 'Scope when 'Scope :> ILocalScope<_> and 'Scope : not struct) = scope.Invoke Scope

type Pool<'T> = {
    maxCount: int
    items: 'T ConcurrentBag
    create: unit -> 'T
    drop: 'T -> unit
}

module Pool =
    let create maxCount create drop = {
        maxCount = maxCount
        items = ConcurrentBag()
        create = create
        drop = drop
    }

    let rentManual pool =
        let mutable r = Unchecked.defaultof<_>
        if pool.items.TryTake &r then r
        else pool.create()

    let returnManual pool x =
        pool.drop x
        if pool.items.Count < pool.maxCount then
            pool.items.Add x

    let inline using pool scope =
        let x = rentManual pool
        let r = scope x
        returnManual pool x
        r

    let inline usingProtected pool scope =
        let x = rentManual pool
        try scope x
        finally returnManual pool x
