"use strict"

import * as path from "path"
import { ExtensionContext, window as Window, workspace } from "vscode"
import { LanguageClient, LanguageClientOptions, RevealOutputChannelOn, ServerOptions, Executable, TransportKind } from "vscode-languageclient"

let client: LanguageClient | null = null

function getPlatform() {
    switch (process.platform) {
        // mac os
        case "darwin":
            switch (process.arch) {
                case "x64": return { rid: "osx-x64" }
            }
        case "linux":
            switch (process.arch) {
                case "x64": return { rid: "linux-x64" }
                case "ia32": return { rid: "linux-x86" }
                case "arm": return { rid: "linux-arm" }
            }
        case "win32":
            switch (process.arch) {
                case "x64": return { rid: "win-x64", extension: ".exe" }
                case "ia32": return { rid: "win-x86", extension: ".exe" }
                case "arm": return { rid: "win-arm", extension: ".exe" }
            }
    }
    throw new Error(`not implemented: '${process.platform}', '${process.arch}'`)
}

export function activate(context: ExtensionContext): void {
    const serverProjectDir = context.asAbsolutePath(path.join("server", "src", "server"))
    const { rid, extension = "" } = getPlatform()
    const serverPath = path.join(
        serverProjectDir, "bin", "Release", "net5.0",
        rid, "publish", "server" + extension
    )
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
