module LuaChecker.Server.Log
open Cysharp.Text
open System
open System.Diagnostics
open System.Runtime.CompilerServices
open System.Runtime.ExceptionServices
open System.IO


type DetailLevel =
    | Output = 0uy
    | Error = 1uy
    | Warning = 2uy
    | Info = 3uy
    | Debug = 4uy
    | Trace = 5uy

type Event = {
    source: string
    stackTrace: StackTrace
    level: DetailLevel
    message: char ReadOnlyMemory
    time: DateTime
}
[<AbstractClass>]
type Logger() =
    interface IDisposable with
        member x.Dispose() =
            x.Dispose(disposing = true)
            GC.SuppressFinalize x

    override x.Finalize() = x.Dispose(disposing = false)

    abstract IsEnabled: DetailLevel -> bool
    default _.IsEnabled _ = true

    abstract Log: Event -> unit

    abstract Dispose: disposing: bool -> unit
    default _.Dispose _ = ()

[<AutoOpen>]
module private Helpers =
    type LoggerMessage =
        | Log of Event
        | Add of Logger
        | Shutdown

    type LoggerState = {
        nextLoggerId: int64
        children: Map<int64, Logger>
    }
    module LoggerState =
        let defaultValue = {
            nextLoggerId = 0L
            children = Map.empty
        }

    let shutdown state =
        let mutable e0 = null
        let mutable es = []
        for kv in state.children do
            try (kv.Value :> IDisposable).Dispose()
            with e ->
                if isNull e0 then e0 <- ExceptionDispatchInfo.Capture e
                es <- e::es

        match es with
        | [] -> ()
        | [_] -> e0.Throw()
        | _ -> raise <| AggregateException es

    let addLogger state x =
        { state with
            nextLoggerId = state.nextLoggerId + 1L
            children = Map.add state.nextLoggerId x state.children
        }

    let backgroundLogger() = MailboxProcessor.Start <| fun inbox ->
        let rec loop state = async {
            match! inbox.Receive() with
            | Shutdown -> shutdown state
            | Add x -> do! loop (addLogger state x)
            | Log event ->
                for kv in state.children do
                    let c = kv.Value
                    if c.IsEnabled event.level then
                        c.Log event
                do! loop state
        }
        async {
            do! Async.SwitchToNewThread()
            do! loop LoggerState.defaultValue
        }

    let showLevel = function
        | DetailLevel.Output -> "Output"
        | DetailLevel.Error -> "Error"
        | DetailLevel.Warning -> "Warning"
        | DetailLevel.Info -> "Information"
        | DetailLevel.Debug -> "Debug"
        | DetailLevel.Trace -> "Trace"
        | _ -> ""

type StreamLogger(stream: Stream) =
    inherit Logger()
    let writer = new StreamWriter(stream = stream)

    override _.Log event =
        let b = ZString.CreateUtf8StringBuilder()
        b.AppendFormat("[{0:O}] {1} : {2} : {3}", event.time, event.source, showLevel event.level, event.message)
        b.AppendLine()
        if DetailLevel.Output < event.level && event.level <= DetailLevel.Error then
            b.AppendLine event.stackTrace

        if stream.CanSeek then stream.Seek(0L, SeekOrigin.End) |> ignore
        stream.Write(b.AsSpan())
        stream.Flush()

    override _.Dispose disposing =
        if disposing then
            writer.Dispose()

[<Sealed>]
type BackgroundLogger(sourceName, initialMaxDetail) =
    inherit Logger()

    let source = sourceName
    let bg = backgroundLogger()

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    let logCore level message =
        let trace = StackTrace(skipFrames = 1, fNeedFileInfo = true)
        let event = {
            source = source
            stackTrace = trace
            level = level
            message = message
            time = DateTime.Now
        }
        bg.Post <| Log event

    member val internal MaxDetail = initialMaxDetail with get, set

    override x.IsEnabled level = level <= x.MaxDetail
    override _.Log e = bg.Post <| Log e
    override _.Dispose disposing = if disposing then bg.Post Shutdown

    member private x.Log(level, message) =
        if level <= x.MaxDetail then
            logCore level message

    member internal x.Log(level, message) =
        x.Log(level, MemoryExtensions.AsMemory message)

    member internal _.Add child = bg.Post <| Add child

module Logger =
    let streamLogger stream = new StreamLogger(stream)

    let fileLogger filePath =
        let stream = new FileStream(filePath, FileMode.Append, FileAccess.Write, FileShare.ReadWrite, 4096, FileOptions.SequentialScan);
        streamLogger stream

    let consoleLogger() = Console.OpenStandardOutput() |> streamLogger
    let standardErrorLogger() = Console.OpenStandardError() |> streamLogger
    let debugLogger() = { new Logger() with
        member _.Log event =
            Debug.WriteLine("[{0:O}] {1} : {2} : {3}", event.time, event.source, showLevel event.level, event.message)
            Debug.Flush()
    }

    let create sourceName maxDetail = new BackgroundLogger(sourceName, maxDetail)
    let isEnabled (logger: Logger) level = logger.IsEnabled level
    let add (logger: BackgroundLogger) child = logger.Add child
    let log (logger: BackgroundLogger) level message = logger.Log(level, message)
    let setMaxDetail (logger: BackgroundLogger) maxDetail = logger.MaxDetail <- maxDetail

let logger = Logger.create "<server>" DetailLevel.Trace
Logger.add logger <| Logger.fileLogger "server.log"
Logger.add logger <| Logger.standardErrorLogger()
Logger.add logger <| Logger.debugLogger()

let inline trace format =
    Printf.ksprintf (fun x c -> Logger.log logger c x) format
type Log =
    static member inline Format format = fun c -> Logger.log logger c format
    static member inline Format(format, arg0) = fun c -> Log.Format(ZString.Format(format, arg0)) c
    static member inline Format(format, arg0, arg1) = fun c -> Log.Format(ZString.Format(format, arg0, arg1)) c
    static member inline Format(format, arg0, arg1, arg2) = fun c -> Log.Format(ZString.Format(format, arg0, arg1, arg2)) c

[<Struct>]
type LoggerConditionalActionBuilder = { trace: Logger; traceEvent: DetailLevel }
with
    member inline _.Zero() = fun _ -> ()
    member inline _.Combine(x, y) = fun c -> x c; y c
    member inline _.Yield x = x
    member inline _.Delay x = x
    member inline b.Run x =
        if Logger.isEnabled b.trace b.traceEvent then
            x () b.traceEvent

let ifOutput = { trace = logger; traceEvent = DetailLevel.Output }
let ifError = { trace = logger; traceEvent = DetailLevel.Error }
let ifWarn = { trace = logger; traceEvent = DetailLevel.Warning }
let ifInfo = { trace = logger; traceEvent = DetailLevel.Info }
let ifDebug = { trace = logger; traceEvent = DetailLevel.Debug }
let ifTrace = { trace = logger; traceEvent = DetailLevel.Trace }
