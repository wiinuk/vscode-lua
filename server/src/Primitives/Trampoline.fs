namespace LuaChecker.Primitives
open System.Runtime.CompilerServices


[<RequireQualifiedAccess>]
type TrampolineTag =
    | Done
    | Failure
    | TailCall
    | Continue

[<Struct>]
type Trampoline<'T,'Error> when 'Error : not struct private (restOrContinueOrDoneTagOrError: obj, valueOrDefault: 'T) =
    static let doneTag = obj()
    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    static member internal makeDone(value: 'T) = Trampoline<'T,'Error>(doneTag, value)
    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    static member internal makeFailure(error: 'Error) = Trampoline<'T,'Error>(error, Unchecked.defaultof<_>)
    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    static member internal makeTailCall(rest: unit -> Trampoline<'T,'Error>) = Trampoline<'T,'Error>(rest, Unchecked.defaultof<_>)
    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    static member internal makeContinue(x: Trampoline<'X,'Error>, f: 'X -> Trampoline<'T,'Error>) =
        Trampoline<'T,'Error>(
            { new TrampolineContinue<'T,'Error>() with member _.Match m = m.Continue(x, f) },
            Unchecked.defaultof<_>
        )

    member _.Tag =
        if LanguagePrimitives.PhysicalEquality restOrContinueOrDoneTagOrError doneTag then TrampolineTag.Done
        elif restOrContinueOrDoneTagOrError :? TrampolineContinue<'T,'Error> then TrampolineTag.Continue
        elif restOrContinueOrDoneTagOrError :? unit -> Trampoline<'T,'Error> then TrampolineTag.TailCall
        else TrampolineTag.Failure

    member _.UncheckedDone = valueOrDefault
    member _.UncheckedFailure = restOrContinueOrDoneTagOrError :?> 'Error
    member _.UncheckedTailCall = restOrContinueOrDoneTagOrError :?> unit -> Trampoline<'T,'Error>
    member _.UncheckedContinue = restOrContinueOrDoneTagOrError :?> TrampolineContinue<'T,'Error>

and [<AbstractClass>] TrampolineContinue<'T,'Error> when 'Error : not struct () =
    abstract Match: 'M byref -> 'R when 'M :> ITrampolineContinueMatcher<'T,'Error,'R> and 'M : struct

and ITrampolineContinueMatcher<'T,'Error,'Result> when 'Error : not struct =
    abstract Continue<'X> : Trampoline<'X,'Error> * ('X -> Trampoline<'T,'Error>) -> 'Result

module rec Trampoline =
    /// 追加のヒープ確保なし
    let Done x = Trampoline.makeDone x
    /// 追加のヒープ確保なし
    let Failure error = Trampoline.makeFailure error
    /// 追加のヒープ確保なし
    let TailCall rest = Trampoline.makeTailCall rest
    /// ヒープ確保あり
    let Continue(x, f) = Trampoline.makeContinue(x, f)

    let ofResult = function Ok x -> Done x | Error e -> Failure e

    let rec private bind (x: Trampoline<_,_>) f =
        match x.Tag with
        | TrampolineTag.Done -> TailCall(fun () -> f x.UncheckedDone)
        | TrampolineTag.Failure -> Failure x.UncheckedFailure
        | TrampolineTag.TailCall -> Continue(x, f)
        | TrampolineTag.Continue ->
            let mutable m = { BindContinueMatcher.f = f }
            x.UncheckedContinue.Match &m

    [<Struct>]
    type private BindContinueMatcher<'a,'b,'e> when 'e : not struct = {
        f: 'a -> Trampoline<'b,'e>
    }
    with
        interface ITrampolineContinueMatcher<'a,'e,Trampoline<'b,'e>> with
            [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
            member m.Continue(a, f') =
                let f = m.f
                Continue(a, fun x -> bind (f' x) f)

    let run (x: Trampoline<_,_>) =
        let mutable x = x
        let mutable result = Unchecked.defaultof<_>
        while
            match x.Tag with
            | TrampolineTag.Done -> result <- Ok x.UncheckedDone; false
            | TrampolineTag.Failure -> result <- Error x.UncheckedFailure; false
            | TrampolineTag.TailCall -> x <- x.UncheckedTailCall(); true
            | TrampolineTag.Continue ->
                let mutable m = ResultContinueMatcher
                x <- x.UncheckedContinue.Match &m
                true
            do ()
        result

    [<Struct>]
    type private ResultContinueMatcher<'a,'e> when 'e : not struct = | ResultContinueMatcher with
        interface ITrampolineContinueMatcher<'a,'e,Trampoline<'a,'e>> with
            [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
            member _.Continue(a, f) =
                match a.Tag with
                | TrampolineTag.Done -> f a.UncheckedDone
                | TrampolineTag.Failure -> Failure a.UncheckedFailure
                | TrampolineTag.TailCall -> bind (a.UncheckedTailCall()) f
                | TrampolineTag.Continue ->
                    let mutable m = { ResultContinueContinueMatcher.f = f }
                    a.UncheckedContinue.Match &m

    [<Struct>]
    type private ResultContinueContinueMatcher<'a,'b,'e> when 'e : not struct = {
        f: 'a -> Trampoline<'b,'e>
    }
    with
        interface ITrampolineContinueMatcher<'a,'e,Trampoline<'b,'e>> with
            member m.Continue(b, g) =
                let f = m.f
                bind b (fun x -> bind (g x) f)

type TrampolineBuilder = private | TrampolineBuilder with
    member inline _.Return x = Trampoline.Done x
    member inline _.ReturnFrom (x: Trampoline<_,_>) = x
    member inline _.Bind(x: Trampoline<_,_>, f) =
        match x.Tag with
        | TrampolineTag.Done -> f x.UncheckedDone
        | TrampolineTag.Failure -> Trampoline.Failure x.UncheckedFailure
        | _ -> Trampoline.Continue(x, f)

module TrampolineOperators =
    let trampoline = TrampolineBuilder
