namespace LuaChecker
open Cysharp.Text
open LuaChecker.Primitives
open System
open System.Collections.Generic
open System.Runtime.CompilerServices


[<Struct>]
type Span = {
    start: int
    end': int
}

[<Struct>]
type Token<'T,'Trivia> = {
    kind: 'T
    trivia: 'Trivia
}

[<Struct>]
type SepBy<'S,'T> = | SepBy of 'T * ('S * 'T) list

module SepBy =
    let toNonEmptyList = function
        | SepBy(x, []) -> NonEmptyList(x, [])
        | SepBy(x, xs) -> NonEmptyList(x, List.map snd xs)

    let head (SepBy(x, _)) = x
    let last (SepBy(x, xs)) =
        match xs with
        | [] -> x
        | _ -> List.last xs |> snd

    let cons x sep (SepBy(x1, xs)) = SepBy(x, (sep, x1)::xs)
    let rev (SepBy(x, xs) as all) =
        match xs with
        | [] -> all
        | _ ->

        let rec aux accX accSepXs = function
            | [] -> SepBy(accX, accSepXs)
            | (sep, x)::sepXs ->
                aux x ((sep, accX)::accSepXs) sepXs
        aux x [] xs

    let toList (SepBy(x, sepXs)) = x::List.map snd sepXs
    let inline fold folder state (SepBy(x, sepXs)) =
        let s = folder state x
        match sepXs with
        | [] -> s
        | _ -> List.fold (fun s (_, x) -> folder s x) s sepXs

    let inline mapSep sepMapping mapping (SepBy(x, sepXs)) =
        let sepXs =
            match sepXs with
            | [] -> []
            | _ -> List.map (fun (sep, x) -> sepMapping sep, mapping x) sepXs
        SepBy(mapping x, sepXs)

    let inline map mapping x = mapSep (fun x -> x) mapping x
    let inline appendToResizeArray (SepBy(x, sepXs)) (buffer: _ ResizeArray) =
        buffer.Add x
        match sepXs with
        | [] -> ()
        | _ ->
            for _, x in sepXs do
                buffer.Add x

module Span =
    let empty = { start = 0; end' = 0 }
    let isEmpty x = x.end' <= x.start
    let merge x1 x2 =
        match isEmpty x1, isEmpty x2 with
        | true, _ -> x2
        | _, true -> x1
        | _ -> { start = x1.start; end' = x2.end' }

    let inline sepBy measure xs = merge (measure (SepBy.head xs)) (measure (SepBy.last xs))
    let inline list measure = function
        | [] -> empty
        | [x] -> measure x
        | x::xs -> merge (measure x) (measure (List.last xs))

    let inline tuple2 (measure1, measure2) (x1, x2) =
        merge (measure1 x1) (measure2 x2)

    let inline option measure = function
        | None -> empty
        | Some x -> measure x

    let inRange i x = x.start <= i && i < x.end'
    let isIntersecting x1 x2 = inRange x1.start x2 || inRange x2.start x1

/// absolute/normalized uri
[<Struct>]
type DocumentPath = private DocumentPath of string
module DocumentPath =
    open System.IO

    let toUri(DocumentPath x) = Uri x
    let toUriString(DocumentPath x) = x
    let toPathOrNone localFileUri =
        let uri = toUri localFileUri
        if uri.IsFile && uri.IsLoopback then ValueSome uri.LocalPath
        else ValueNone

    let toPathOrFail localFileUri =
        match toPathOrNone localFileUri with
        | ValueSome x -> x
        | _ -> invalidArg (nameof localFileUri) $"local file URI is required: {localFileUri}"

    let ofUri (absoluteUri: Uri) =
        if not absoluteUri.IsAbsoluteUri then
            invalidArg (nameof absoluteUri) $"absolute URI is required: {absoluteUri}"

        string absoluteUri |> Uri.UnescapeDataString |> DocumentPath

    let ofRelativeUri (baseUri: Uri) (relativeOrAbsoluteUri: Uri) =
        if not relativeOrAbsoluteUri.IsAbsoluteUri
        then Uri(baseUri, relativeOrAbsoluteUri)
        else relativeOrAbsoluteUri
        |> ofUri

    let ofPath absoluteOSPath =
        if not <| Path.IsPathFullyQualified(absoluteOSPath + "") then
            invalidArg (nameof absoluteOSPath) $"fully qualified path is required: {absoluteOSPath}"

        UriBuilder("file", "", Path = absoluteOSPath).Uri |> ofUri

    let equalityComparer caseSensitive =
        if caseSensitive then
            { new IEqualityComparer<_> with
            override _.Equals(DocumentPath x, DocumentPath y) = String.Equals(x, y)
            override _.GetHashCode(DocumentPath x) = x.GetHashCode()
            }
        else
            let comparer = StringComparer.OrdinalIgnoreCase
            { new IEqualityComparer<_> with
            override _.Equals(DocumentPath x, DocumentPath y) = String.Equals(x, y, StringComparison.OrdinalIgnoreCase)
            override _.GetHashCode(DocumentPath x) = comparer.GetHashCode x
            }

[<Struct>]
type Location = Location of DocumentPath * Span

[<RequireQualifiedAccess>]
type FieldKey =
    | String of string
    | Number of double
    | Bool of bool

module FieldKey =
    let show = function
        | FieldKey.Bool x -> x.ToString()
        | FieldKey.Number x -> x.ToString "G17"
        | FieldKey.String x -> x

[<Extension>]
type FieldKeyExtensions =
    [<Extension>]
    static member Append(b: Utf16ValueStringBuilder byref, x) =
        match x with
        | FieldKey.Bool true -> b.Append "true"
        | FieldKey.Bool false -> b.Append "false"
        // TODO: NaN, +inf, -inf
        | FieldKey.Number x -> b.Append(x, "G17")
        // TODO: null
        | FieldKey.String x -> b.Append x
