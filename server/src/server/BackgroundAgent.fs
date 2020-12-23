[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module LuaChecker.Server.BackgroundAgent
open LuaChecker
open LuaChecker.Server.Log
open LuaChecker.Server.Protocol
open LuaChecker.Text.Json
open System
open System.Collections.Immutable
open type Marshalling.CollectSemanticsVisitor
open type Marshalling.MarshallingContext
open type Marshalling.PrettyTokenVisitor
open type ProjectAgent
open type BackgroundAgent
open type TypedSyntaxes.Chunk
open type TypeSystem.TypeEnv
type private M = Protocol.Methods


let sendNotification agent methods parameters =
    let jsonBytes =
        JsonRpcMessage.notification methods parameters
        |> Json.serialize
        |> ReadOnlyMemory

    agent.writeAgent.Post <| WriteMessage jsonBytes

let publishDiagnostics agent projectAgent path version document diagnostics =
    let diagnostics =
        match document with
        | ValueNone -> [||]
        | ValueSome document ->

        let context = {
            documents = projectAgent.documents
            resources = agent.resources
            root = projectAgent.root
        }
        Seq.toArray <| Marshalling.marshalDocumentDiagnostics context path document diagnostics

    {
        uri = DocumentPath.toUri(path).ToString()
        version = Defined version
        diagnostics = diagnostics
    }
    |> ValueSome
    |> sendNotification agent
        M.``textDocument/publishDiagnostics``

let hoverHitTestAndResponse requestId projectAgent document { Token.kind = { TypedSyntaxes.semanticTree = tree } } position =
    let index = Document.positionToIndex position document
    let context = {
        root = projectAgent.root
        resources = projectAgent.resources
        documents = projectAgent.documents
    }
    let mutable this = {
        marshallingContext = context
        renderedText = ""
    }
    let result =
        if Block.hitTest &this index tree then
            let markdown = { kind = MarkupKind.markdown; value = this.renderedText }
            ValueSome { contents = markdown; range = Undefined }
        else
            ValueNone

    WriteAgent.sendResponse projectAgent.writeAgent requestId (Ok result)

let responseSemanticTokens ({ semanticTokensDataBuffer = buffer } as agent) x =
    ifDebug { agent.watch.Restart() }
    let {
        requestId = id
        writeAgent = writeAgent
        document = { lineMap = Lazy lineMap }
        tree = tree
        project = project
        rangeOrFull = rangeOrFull
        } = x

    let range =
        match rangeOrFull with
        | ValueSome range -> Marshalling.rangeToSpan lineMap range
        | _ -> tree.trivia

    let initialGlobal = project.projectRare.initialGlobal
    let typeEnv = {
        system = initialGlobal.typeSystem
        stringTableTypes =
            tree.kind.additionalGlobalEnv.stringMetaTableIndexType @
            initialGlobal.initialGlobalEnv.stringMetaTableIndexType
    }
    let mutable this = {
        buffer = buffer
        lineMap = lineMap
        typeSystemEnv = typeEnv
        lastLine = 0
        lastStartChar = 0
    }
    Block.iterateRange &this range tree.kind.semanticTree |> ignore
    WriteAgent.sendResponse writeAgent id <| Ok {
        resultId = Undefined
        data = buffer.ToArray()
    }
    buffer.Clear()
    ifDebug { trace $"semantic tokens calculation complete: {agent.watch.ElapsedMilliseconds}ms" }

let create agent = new MailboxProcessor<_>(fun inbox ->
    let rec loop agent = async {
        match! inbox.Receive() with
        | QuitBackgroundAgent -> return ()
        | PublishDiagnostics(projectAgent, path, version, document, diagnostics) ->
            publishDiagnostics agent projectAgent path version document diagnostics
            return! loop agent

        | HoverHitTestAndResponse(id, projectAgent, document, tree, position) ->
            hoverHitTestAndResponse id projectAgent document tree position
            return! loop agent

        | EnumerateFiles(fs, dir, dest) ->
            fs.enumerateFiles (DocumentPath.ofUri dir) |> ImmutableArray.CreateRange |> EnumerateFilesResponse |> dest.Post
            return! loop agent

        | ResponseSemanticTokens x ->
            responseSemanticTokens agent x
            return! loop agent
    }
    loop agent
)
