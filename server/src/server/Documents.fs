namespace LuaChecker.Server
open LuaChecker
open LuaChecker.Server.Log
open LuaChecker.Server.Protocol
open LuaChecker.Text.Json
open System


type Document = {
    contents: string
    version: int
    lineMap: LineMap Lazy
}
module Document =
    let create version contents = { contents = contents; version = version; lineMap = lazy LineMap.create contents }
    let positionToIndex { line = line; character = char } { lineMap = Lazy lineMap } =
        LineMap.lineStartPosition line lineMap + char

    let changeRange { start = start; ``end`` = end' } newVersion newText d =
        let start = positionToIndex start d
        let end' = positionToIndex end' d
        d.contents.Remove(start, end' - start).Insert(start, newText)
        |> create newVersion

type Documents = Map<DocumentPath, Document>
module Documents =
    let openedPaths documents = Map.toSeq documents |> Seq.map fst
    let tryFind path documents = Map.tryFind path documents
    let open' path text version documents =
        let document = Document.create version text
        Map.add path document documents

    let change path version changes documents =
        match version with
        | ValueNone ->
            ifDebug { trace "change ignored: %A" path }
            documents

        | ValueSome version ->

        match Map.tryFind path documents with
        | ValueNone -> documents
        | ValueSome document ->

        if version <= document.version then
            ifDebug { trace "received old version change" }
            documents
        else

        let document =
            changes
            |> Array.fold (fun document { text = text; range = range } ->
                match range with
                | Undefined -> Document.create version text
                | Defined range -> Document.changeRange range version text document
            ) document

        Map.add path document documents

    let close path documents = Map.remove path documents
