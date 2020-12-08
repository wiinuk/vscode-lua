namespace LuaChecker
open System


[<Struct>]
type LineMap = LineMap of lineStarts: int array

[<Struct>]
type Position = Position of line: int * character: int

module LineMap =
    let create source =
        let rec aux (lineStarts: _ ResizeArray) lineStart (source: string) =
            let i = source.IndexOf('\n', startIndex = lineStart)
            if 0 <= i then
                lineStarts.Add lineStart
                aux lineStarts (i + 1) source
            else
                lineStarts.Add lineStart
                lineStarts

        (aux (ResizeArray()) 0 source).ToArray() |> LineMap

    let findLine position (LineMap lineStarts) =
        match lineStarts.Length with
        | 0 -> 0
        | 1 -> 0
        | _ ->
            let line = Array.BinarySearch(lineStarts, 1, lineStarts.Length - 1, position)
            if line < 0 then ~~~line - 1 else line

    let findPosition position (LineMap lineStarts as lineMap) =
        let line = findLine position lineMap
        Position(
            line = line,
            character = position - lineStarts.[line]
        )

    let lineStartPosition lineNumber (LineMap lineStarts) =
        let lineNumber = max (min lineNumber (lineStarts.Length - 1)) 0
        lineStarts.[lineNumber]
