module LuaChecker.TolerantParserCombinator
open System.ComponentModel
open LuaChecker.Syntax


let inline list isTerminator p s =
    let mutable acc = []
    while not (isTerminator s || Scanner.tokenKind s = TokenKind.Unknown) do acc <- p s::acc
    List.rev acc

let inline tuple2 (p1, p2) s = p1 s, p2 s
let inline option canParse p s = if canParse s then Some(p s) else None

let inline sepByCore makeState foldState finishState isTerminator sepP p s =
    let x = p s
    let mutable state = makeState x
    while not (isTerminator s || Scanner.tokenKind s = TokenKind.Unknown) do
        state <- foldState state (sepP s) (p s)
    finishState x state

let inline sepBy isTerminator sepP p s =
    sepByCore
        (fun _ -> []) (fun acc sep x -> (sep, x)::acc) (fun x acc -> struct(x, List.rev acc))
        isTerminator sepP p s

/// `p (op p)*`
let inline chainL isTerminator p op f s =
    sepByCore
        (fun x -> x) (fun l op r -> f(l, op, r)) (fun _ x -> x)
        isTerminator op p s

/// `p (op p)*`
let inline chainR isTerminator p op f s =
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
        isTerminator op p s

/// p op*
let inline postfixOps isTerminator p op s =
    let mutable x = p s
    while not (isTerminator s || Scanner.tokenKind s = TokenKind.Unknown) do
        x <- op x s
    x

[<EditorBrowsable(EditorBrowsableState.Never)>]
let _ensureAndAdd (ops: _ byref) op =
    match ops with
    | null -> ops <- ResizeArray()
    | _ -> ()
    ops.Add op

/// op* p
let inline prefixOps isTerminator reduce op p s =
    // TODO: pool
    let mutable ops = null
    while not (isTerminator s || Scanner.tokenKind s = TokenKind.Unknown) do
        _ensureAndAdd &ops (op s)

    let mutable r = p s

    match ops with
    | null -> r
    | _ ->

    for i = ops.Count-1 downto 0 do
        r <- reduce(ops.[i], r)
    r
