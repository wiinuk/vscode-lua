namespace LuaChecker.Test
open System
open Xunit
open Xunit.Sdk

module Diff =
    open DiffPlex
    open DiffPlex.DiffBuilder
    open DiffPlex.DiffBuilder.Model
    open System.Text.RegularExpressions
    type private C = Model.ChangeType

    let private reduceWords (ds: DiffPaneModel) =
        ds.Lines
        |> Seq.map (fun p -> p.Type, p.Text)
        |> Seq.fold (fun ((lastType, lastWordsRev), chunksRev) (t, s) ->
            if lastType = t then
                (lastType, s::lastWordsRev), chunksRev
            else
                (t, [s]), (lastType, lastWordsRev)::chunksRev
        ) ((C.Unchanged, []), [])
        |> function (chunk, chunksRev) -> List.rev (chunk::chunksRev)
        |> Seq.map (fun (change, wordsRev) -> change, List.rev wordsRev)

    let printDiffLine ds =
        let o = obj()
        let writeWithColor c x = lock o <| fun _ ->
            let c' = Console.ForegroundColor
            Console.ForegroundColor <- c
            Console.Write (x + "")
            Console.ForegroundColor <- c'

        reduceWords ds
        |> Seq.iter (fun (c, words) ->
            let text = words |> String.concat ""
            match c with
            | C.Deleted -> writeWithColor ConsoleColor.Red text
            | C.Inserted -> writeWithColor ConsoleColor.Green text
            | C.Modified
            | C.Imaginary
            | C.Unchanged
            | _ -> Console.Write text
        )
        printfn ""

    let prettyDiff ds =
        ds
        |> reduceWords
        |> Seq.collect (fun (c, words) -> seq {
            match c with
            | C.Deleted -> "[- "; yield! words; " -]"
            | C.Inserted -> "[+ "; yield! words; " +]"
            | C.Modified
            | C.Imaginary
            | C.Unchanged
            | _ -> yield! words
        })
        |> String.concat ""

    let diffWords text1 text2 =
        InlineDiffBuilder.Diff(
            text1,
            text2,
            ignoreWhiteSpace = false,
            chunker = { new IChunker with member _.Chunk xs = Regex.Split(input = xs, pattern = "(\s+)") }
        )

[<AutoOpen>]
module AssertHelpers =
    let (=?) actual expected =
        if not (LanguagePrimitives.GenericEqualityER actual expected) then
            let act = $"%0A{actual}"
            let exp = $"%0A{expected}"
            let diff = Diff.diffWords act exp
            raise <| AssertActualExpectedException(exp, act, $"{nameof diff}:{Diff.prettyDiff diff}\n{nameof actual}:\n{act}\n{nameof expected}:\n{exp}")

    let (<>?) l r =
        if not (l <> r) then
            Assert.NotEqual<'a>(l, (r: 'a), LanguagePrimitives.FastGenericEqualityComparer<'a>)

    let equalsWithMessage (actual, expected) format =
        Printf.ksprintf (fun message ->
            if not (LanguagePrimitives.GenericEqualityER actual expected) then
                let act = $"%0A{actual}"
                let exp = $"%0A{expected}"
                let diff = Diff.diffWords act exp
                failwith $"{nameof diff}:\n{Diff.prettyDiff diff}\n{nameof actual}:\n{act}\n{nameof expected}:\n{exp}\n{nameof message}: {message}"
        ) format
