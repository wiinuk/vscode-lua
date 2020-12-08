import * as path from "path"
import { ExtensionContext, window as Window, workspace } from "vscode"
import { LanguageClient, LanguageClientOptions, RevealOutputChannelOn, ServerOptions, Executable, TransportKind } from "vscode-languageclient"
import * as supportedRuntimeSpecs from "./supported-runtime-specs.json"

let client: LanguageClient | null = null

function getPlatform() {
    const { platform, arch } = process

    const spec = supportedRuntimeSpecs.find(runtime =>
        runtime.platform === platform && runtime.arch === arch
    )
    if (spec) { return spec }

    throw new Error(`not implemented: '${platform}', '${arch}'`)
}

export function activate(context: ExtensionContext): void {
    const serverProjectDir = context.asAbsolutePath(path.join("server", "src", "server"))
    const { rid, platform } = getPlatform()
    const extension = platform === "win32" ? ".exe" : ""

    const serverPath = context.asAbsolutePath(path.join("server", "bin", rid, "server" + extension))
    const serverCommand: Executable = {
        command: serverPath,
        args: [],
        options: {
            cwd: process.cwd(),
        },
    }
    const debugCommand: Executable = {
        command: "dotnet",
        args: ["run"],
        options: {
            cwd: serverProjectDir,
            shell: true,
            env: {
                ...process.env,
                ["DOTNET_CLI_UI_LANGUAGE"]: "en",
            },
        }
    }
    const serverOptions: ServerOptions = {
        run: serverCommand,
        debug: debugCommand,
        transport: TransportKind.stdio,
    }
    const clientOptions: LanguageClientOptions = {
        documentSelector: [{ scheme: "file", language: "lua", }],
        diagnosticCollectionName: "sample",
        revealOutputChannelOn: RevealOutputChannelOn.Never,
        synchronize: {
            fileEvents: [
                workspace.createFileSystemWatcher("**/*.lua")
            ]
        }
    }

    try {
        client = new LanguageClient("Lua LSP Server", serverOptions, clientOptions)
    }
    catch (err) {
        Window.showErrorMessage("The extension couldn't be started. See the output channel for details.")
        return
    }
    client.registerProposedFeatures()

    context.subscriptions.push(
        client.start(),
    )
}

export function deactivate(): Thenable<void> | undefined {
    if (!client) { return }
    return client.stop()
}
