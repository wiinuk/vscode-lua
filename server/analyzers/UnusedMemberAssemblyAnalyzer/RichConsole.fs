module LuaChecker.Analyzers.RichConsole
open FSharp.Compiler.SourceCodeServices
open Spectre.Console
open Spectre.Console.Rendering
open System


module StylePallet =
    let sourceLocation = Style(foreground = Color.Grey)
    let number = Style(foreground = Color.Green)
    let plain = Style.Plain

let mutable Styles = {|
    plain = StylePallet.plain

    sourceLocation = StylePallet.sourceLocation

    string = Style(foreground = Color.Yellow)
    keyword = Style(decoration = Decoration.Bold)
    comment = Style(foreground = Color.Green)
    number = StylePallet.number
    typeName = Style(foreground = Color.Green)
    memberName = Style(foreground = Color.DarkOrange)
    nameSpace = StylePallet.plain
    label = StylePallet.sourceLocation
    opcode = StylePallet.number

    delimiter = StylePallet.sourceLocation
    operator = StylePallet.sourceLocation

    missing = Style(foreground = Color.Red)

    hint = Style(foreground = Color.Blue)
|}

[<Struct>]
type Run = private Run of markup: string seq with
    override x.ToString() =
        let (Run xs) = x
        let c = RenderContext(System.Text.Encoding.Unicode, legacyConsole = false)
        seq {
            for x in xs do
                for s in (Markup x :> IRenderable).Render(c, System.Int32.MaxValue) do
                    s.Text
        }
        |> String.concat ""

module Run =
    module Operators =
        let (++) (Run xs1) (Run xs2) = Run(Seq.append xs1 xs2)

    let empty = Run []
    let lineBreak = Run [Markup.Escape System.Environment.NewLine]
    let styled (style: Style) text =

        match style.ToMarkup() with
        | "" -> Run [Markup.Escape text]
        | style -> Run [$"[{style}]{Markup.Escape text}[/]"]

    let whitespace = styled Styles.plain " "
    let plain x = styled Styles.plain x
    let write (console: IAnsiConsole) (Run xs) =
        let x = Markup(String.concat "" xs) :> IRenderable
        AnsiConsole.Console.Write(x.Render(RenderContext(System.Text.Encoding.Unicode, legacyConsole = false), System.Int32.MaxValue))

    let print x = write AnsiConsole.Console x
    let printLine x = Operators.(++) x lineBreak |> print
    let markup (Run xs) = String.concat "" xs
    let ofMarkup markup = Run [markup]


let singleSegment text =
    { new IRenderable with
        member _.Measure(_, _) = Measurement(String.length text, text.Length)
        member _.Render(_, _) = upcast [Segment text]
    }

let tokenizer = FSharpSourceTokenizer([], None)
let printLineTokens state line hasTrainlingNewLine =
    let lineTokenizer = tokenizer.CreateLineTokenizer line
    let mutable state = state
    let mutable consumedLength = 0
    while
        begin
            match lineTokenizer.ScanToken state with
            | Some token, state' ->
                let style =
                    match token.ColorClass with
                    | FSharpTokenColorKind.InactiveCode -> Styles.label
                    | FSharpTokenColorKind.Comment -> Styles.comment
                    | FSharpTokenColorKind.Keyword -> Styles.keyword
                    | FSharpTokenColorKind.Number -> Styles.number
                    | FSharpTokenColorKind.Operator -> Styles.operator
                    | FSharpTokenColorKind.PreprocessorKeyword -> Styles.memberName
                    | FSharpTokenColorKind.Punctuation -> Styles.delimiter
                    | FSharpTokenColorKind.String -> Styles.string
                    | FSharpTokenColorKind.Identifier
                    | FSharpTokenColorKind.UpperIdentifier
                    | FSharpTokenColorKind.Text
                    | _ -> Styles.plain

                consumedLength <- consumedLength + token.FullMatchedLength
                AnsiConsole.Render(Text(line.[token.LeftColumn..token.RightColumn], style))

                state <- state'
                true

            | _, state' ->
                state <- state'
                false
        end do ()

    if consumedLength <> line.Length then
        AnsiConsole.Render(Text(line.[consumedLength..], Styles.plain))

    if hasTrainlingNewLine then
        AnsiConsole.WriteLine()
    state

let printTokens source =
    let mutable state = FSharpTokenizerLexState.Initial
    let mutable remaining = (source + "").AsSpan()
    while
        begin
            let index = remaining.IndexOf '\n'
            if index < 0 then
                state <- printLineTokens state (remaining.ToString()) false
                false
            else
                let line = remaining.Slice(0, index)
                remaining <- remaining.Slice(index + 1)
                state <- printLineTokens state (line.ToString()) true
                true
        end
        do ()

let printf format = Printf.kprintf printTokens format
let printfn format = Printf.kprintf (fun message -> printTokens message; AnsiConsole.WriteLine()) format
