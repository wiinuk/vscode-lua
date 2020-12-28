module LuaChecker.ParserCombinator
open System.ComponentModel
open System.Diagnostics.CodeAnalysis


let inline list p s =
    let mutable acc = []
    while
        begin
            let state = Scanner.getState s
            match p s with
            | Error _ ->
                Scanner.setState &state s
                false

            | Ok x ->
                acc <- x::acc
                true
        end
        do ()

    Ok(List.rev acc)

let inline pipe2 (p1, p2) f s =
    match p1 s with
    | Error e -> Error e
    | Ok x1 ->

    match p2 s with
    | Error e -> Error e
    | Ok x2 ->

    Ok(f(x1, x2))

let inline tuple2 (p1, p2) s = pipe2 (p1, p2) id s

let inline pipe3 (p1, p2, p3) f s =
    match p1 s with
    | Error e -> Error e
    | Ok x1 ->

    match p2 s with
    | Error e -> Error e
    | Ok x2 ->

    match p3 s with
    | Error e -> Error e
    | Ok x3 ->

    Ok(f(x1, x2, x3))

let inline pipe4 (p1, p2, p3, p4) f s =
    match p1 s with
    | Error e -> Error e
    | Ok x1 ->

    match p2 s with
    | Error e -> Error e
    | Ok x2 ->

    match p3 s with
    | Error e -> Error e
    | Ok x3 ->

    match p4 s with
    | Error e -> Error e
    | Ok x4 ->

    Ok(f(x1, x2, x3, x4))

let inline pipe5 (p1, p2, p3, p4, p5) f s =
    match p1 s with
    | Error e -> Error e
    | Ok x1 ->

    match p2 s with
    | Error e -> Error e
    | Ok x2 ->

    match p3 s with
    | Error e -> Error e
    | Ok x3 ->

    match p4 s with
    | Error e -> Error e
    | Ok x4 ->

    match p5 s with
    | Error e -> Error e
    | Ok x5 ->

    Ok(f(x1, x2, x3, x4, x5))

let inline mapResult f = function
    | Ok x -> Ok(f x)
    | Error e -> Error e

let inline option p s =
    let s' = Scanner.getState s
    match p s with
    | Error _ -> Scanner.setState &s' s; Ok None
    | Ok x -> Ok(Some x)

let inline sepByCore makeState foldState finishState sepP p s =
    match p s with
    | Error e -> Error e
    | Ok x ->

    let mutable state = makeState x
    while
        begin
            let s' = Scanner.getState s
            match sepP s with
            | Error _ -> Scanner.setState &s' s; false
            | Ok sep ->

            match p s with
            | Error _ -> Scanner.setState &s' s; false
            | Ok x ->

            state <- foldState state sep x
            true
        end
        do ()

    Ok(finishState x state)

[<SuppressMessage("UnusedMemberAssemblyAnalyzer", "AA0001:MemberUnused")>]
let inline sepBy sepP p s =
    sepByCore
        (fun _ -> []) (fun acc sep x -> (sep, x)::acc) (fun x acc -> struct(x, List.rev acc))
        sepP p s

/// `p (op p)*`
[<SuppressMessage("UnusedMemberAssemblyAnalyzer", "AA0001:MemberUnused")>]
let inline chainL p op f s =
    sepByCore
        (fun x -> x) (fun l op r -> f(l, op, r)) (fun _ x -> x)
        op p s

/// `p (op p)*`
[<SuppressMessage("UnusedMemberAssemblyAnalyzer", "AA0001:MemberUnused")>]
let inline chainR p op f s =
    sepByCore
        (fun _ -> []) (fun ops op r -> (r, op)::ops) (fun l ops ->
            match ops with
            | [] -> l
            | (r, op)::ops ->
                let mutable op = op
                let mutable r = r
                let mutable ops = ops
                while
                    let l =
                        match ops with
                        | [] -> l
                        | (l, _)::_ -> l
                    in
                    r <- f(l, op, r);
                    match ops with
                    | [] -> false
                    | (_, op')::ops' ->
                        op <- op'
                        ops <- ops'
                        true
                    do ()
                r
        )
        op p s

let inline postfixOps p op s =
    match p s with
    | Error e -> Error e
    | Ok x ->

    let mutable x = x
    while
        begin
            let s' = Scanner.getState s
            match op x s with
            | Ok x' ->
                x <- x'
                true
            | _ ->
                Scanner.setState &s' s
                false
        end
        do ()
    Ok x

[<EditorBrowsable(EditorBrowsableState.Never)>]
let _ensureAndAdd (ops: _ byref) op =
    match ops with
    | null -> ops <- ResizeArray()
    | _ -> ()
    ops.Add op
    true

[<SuppressMessage("UnusedMemberAssemblyAnalyzer", "AA0001:MemberUnused")>]
let inline prefixOps reduce op p s =
    // TODO: pool
    let mutable ops = null
    while
        match op s with
        | Error _ -> false
        | Ok op -> _ensureAndAdd &ops op
        do ()

    let r = p s

    match ops with
    | null -> r
    | _ ->

    match r with
    | Error _ -> r
    | Ok x ->
        let mutable result = x
        for i = ops.Count-1 downto 0 do
            result <- reduce(ops.[i], result)
        Ok result

let inline attempt p s =
    let s' = Scanner.getState s
    match p s with
    | Error _ as r -> Scanner.setState &s' s; r
    | r -> r
