namespace LuaChecker.Primitives


[<Struct>]
type NonEmptyList<'T> = NonEmptyList of 'T * 'T list

module NonEmptyList =
    let head (NonEmptyList(x, _)) = x
    let inline map f (NonEmptyList(x, xs)) =
        let x = f x
        match xs with
        | [] -> NonEmptyList(x, [])
        | _ -> NonEmptyList(x, List.map f xs)

    let toList (NonEmptyList(x, xs)) = x::xs
    let singleton x = NonEmptyList(x, [])
    let cons head (NonEmptyList(x, xs)) = NonEmptyList(head, x::xs)
    let append (NonEmptyList(x1, xs1)) (NonEmptyList(x2, xs2)) =
        match xs1, xs2 with
        | [], [] -> NonEmptyList(x1, [x2])
        | _ -> NonEmptyList(x1, xs1@x2::xs2)

    let inline fold folder state (NonEmptyList(x, xs)) =
        let s = folder state x
        match xs with
        | [] -> s
        | _ -> List.fold folder s xs

    let inline foldBack folder (NonEmptyList(x, xs)) state =
        let state =
            match xs with
            | [] -> state
            | _ -> List.foldBack folder xs state
        folder x state

    let inline forall predicate (NonEmptyList(x, xs)) =
        predicate x && List.forall predicate xs
