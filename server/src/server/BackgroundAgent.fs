[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module LuaChecker.Server.BackgroundAgent
open LuaChecker
open LuaChecker.Server.Log
open LuaChecker.Server.Protocol
open LuaChecker.Text.Json
open System
open System.Collections.Immutable
open type Marshalling.CollectSemanticsThis
open type Marshalling.MarshallingContext
open type Marshalling.PrettyThis
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

let hoverHitTestAndResponse requestId projectAgent document tree position =
    let index = Document.positionToIndex position document
    let context = {
        root = projectAgent.root
        resources = projectAgent.resources
        documents = projectAgent.documents
    }
    let this = {
        marshallingContext = context
        renderedText = ""
    }
    let result =
        if Block.hitTest Marshalling.prettyTokenInfo this index tree.entity then
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
        | _ -> tree.span

    let initialGlobal = project.projectRare.initialGlobal
    let typeEnv = {
        system = initialGlobal.typeSystem
        stringTableTypes =
            tree.state.additionalGlobalEnv.stringMetaTableIndexType @
            initialGlobal.initialGlobalEnv.stringMetaTableIndexType
    }
    let this = {
        buffer = buffer
        lineMap = lineMap
        typeSystemEnv = typeEnv
        lastLine = 0
        lastStartChar = 0
    }
    Block.iterateRange Marshalling.collectSemanticsTokenData this range tree.entity |> ignore
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
