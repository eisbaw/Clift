// Clift VS Code Extension
//
// Entry point. Registers commands and providers for inline verification
// feedback. See spec.md for detailed architecture.
//
// This is a minimal scaffold that registers the commands. Full implementation
// requires the VS Code extension API at runtime.

import * as vscode from 'vscode';

// Verification status per function
interface FunctionStatus {
    name: string;
    module: string;
    status: 'verified' | 'partial' | 'unverified';
    sorryCount: number;
    hasL1Corres: boolean;
    hasFuncSpec: boolean;
}

// Gutter decoration types
let verifiedDecoration: vscode.TextEditorDecorationType;
let partialDecoration: vscode.TextEditorDecorationType;
let unverifiedDecoration: vscode.TextEditorDecorationType;

export function activate(context: vscode.ExtensionContext) {
    console.log('Clift extension activated');

    // Create gutter decoration types
    verifiedDecoration = vscode.window.createTextEditorDecorationType({
        gutterIconPath: context.asAbsolutePath('icons/verified.svg'),
        gutterIconSize: '80%',
        overviewRulerColor: new vscode.ThemeColor('clift.verified'),
    });

    partialDecoration = vscode.window.createTextEditorDecorationType({
        gutterIconPath: context.asAbsolutePath('icons/partial.svg'),
        gutterIconSize: '80%',
        overviewRulerColor: new vscode.ThemeColor('clift.partial'),
    });

    unverifiedDecoration = vscode.window.createTextEditorDecorationType({
        gutterIconPath: context.asAbsolutePath('icons/unverified.svg'),
        gutterIconSize: '80%',
        overviewRulerColor: new vscode.ThemeColor('clift.unverified'),
    });

    // Register commands
    context.subscriptions.push(
        vscode.commands.registerCommand('clift.verifyFunction', verifyFunction),
        vscode.commands.registerCommand('clift.proveWithAI', proveWithAI),
        vscode.commands.registerCommand('clift.showProofChain', showProofChain),
        vscode.commands.registerCommand('clift.importCFile', importCFile),
        vscode.commands.registerCommand('clift.runPipeline', runPipeline),
        vscode.commands.registerCommand('clift.showSorryCount', showSorryCount),
    );

    // Status bar item showing verification coverage
    const statusBarItem = vscode.window.createStatusBarItem(
        vscode.StatusBarAlignment.Left,
        100
    );
    statusBarItem.command = 'clift.showSorryCount';
    statusBarItem.text = '$(shield) Clift: scanning...';
    statusBarItem.show();
    context.subscriptions.push(statusBarItem);

    // Initial scan
    scanVerificationStatus(statusBarItem);

    // Re-scan on file save
    context.subscriptions.push(
        vscode.workspace.onDidSaveTextDocument((doc) => {
            if (doc.languageId === 'lean4' || doc.fileName.endsWith('.lean')) {
                const config = vscode.workspace.getConfiguration('clift');
                if (config.get('autoVerifyOnSave', false)) {
                    scanVerificationStatus(statusBarItem);
                }
            }
        })
    );
}

export function deactivate() {
    console.log('Clift extension deactivated');
}

// --- Command implementations ---

async function verifyFunction() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showWarningMessage('No active editor');
        return;
    }

    const projectRoot = getProjectRoot();
    if (!projectRoot) {
        vscode.window.showErrorMessage('Could not find Clift project root (no lakefile.lean)');
        return;
    }

    const terminal = vscode.window.createTerminal('Clift Build');
    terminal.sendText(`cd "${projectRoot}" && lake build`);
    terminal.show();
}

async function proveWithAI() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showWarningMessage('No active editor');
        return;
    }

    const projectRoot = getProjectRoot();
    if (!projectRoot) {
        vscode.window.showErrorMessage('Could not find Clift project root');
        return;
    }

    const filePath = editor.document.fileName;
    const config = vscode.workspace.getConfiguration('clift');
    const engine = config.get('proofEngine', 'claudecode');

    if (engine === 'none') {
        vscode.window.showInformationMessage('AI proof engine disabled in settings');
        return;
    }

    vscode.window.withProgress(
        {
            location: vscode.ProgressLocation.Notification,
            title: 'Clift: Proving with AI...',
            cancellable: true,
        },
        async (progress, token) => {
            const terminal = vscode.window.createTerminal('Clift Prove');
            terminal.sendText(
                `cd "${projectRoot}" && python3 clift-prove-by-claudecode "${filePath}" --project-dir . -v`
            );
            terminal.show();
        }
    );
}

async function showProofChain() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showWarningMessage('No active editor');
        return;
    }

    // Extract function name from current cursor position
    const line = editor.document.lineAt(editor.selection.active.line).text;
    const match = line.match(/def\s+(\w+)_body/);
    const funcName = match ? match[1] : 'unknown';

    const panel = vscode.window.createWebviewPanel(
        'cliftProofChain',
        `Proof Chain: ${funcName}`,
        vscode.ViewColumn.Beside,
        { enableScripts: true }
    );

    panel.webview.html = getProofChainHtml(funcName);
}

async function importCFile() {
    const files = await vscode.window.showOpenDialog({
        canSelectMany: false,
        filters: { 'C Source': ['c', 'h'] },
        title: 'Select C file to import',
    });

    if (!files || files.length === 0) return;

    const cFile = files[0].fsPath;
    const projectRoot = getProjectRoot();
    if (!projectRoot) {
        vscode.window.showErrorMessage('Could not find Clift project root');
        return;
    }

    const baseName = cFile.replace(/.*\//, '').replace(/\.c$/, '');
    const moduleName = baseName.charAt(0).toUpperCase() + baseName.slice(1);

    const terminal = vscode.window.createTerminal('Clift Import');
    terminal.sendText(`cd "${projectRoot}" && just import "${cFile}" ${moduleName}`);
    terminal.show();
}

async function runPipeline() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) return;

    // Try to extract module name from file path
    const filePath = editor.document.fileName;
    const match = filePath.match(/Generated\/(\w+)\.lean/);
    if (!match) {
        vscode.window.showWarningMessage('Open a Generated/*.lean file to run the pipeline');
        return;
    }

    const moduleName = match[1];
    vscode.window.showInformationMessage(`Running clift pipeline for ${moduleName}...`);
    // Pipeline is run via lake build (the clift command is in Lean)
}

async function showSorryCount() {
    const projectRoot = getProjectRoot();
    if (!projectRoot) {
        vscode.window.showErrorMessage('Could not find Clift project root');
        return;
    }

    const terminal = vscode.window.createTerminal('Clift Sorry Count');
    terminal.sendText(
        `cd "${projectRoot}" && echo "=== Sorry count ===" && ` +
        `grep -rn "sorry" Clift/ Examples/ Generated/ --include="*.lean" | ` +
        `grep -v "^.*:.*--" | grep -v "sorry-free" | grep -v "no sorry" | ` +
        `grep -v "zero sorry" | grep -v "Sorry" | wc -l`
    );
    terminal.show();
}

// --- Helper functions ---

function getProjectRoot(): string | undefined {
    const config = vscode.workspace.getConfiguration('clift');
    const configured = config.get<string>('projectRoot');
    if (configured) return configured;

    // Auto-detect from workspace
    const folders = vscode.workspace.workspaceFolders;
    if (folders) {
        return folders[0].uri.fsPath;
    }
    return undefined;
}

async function scanVerificationStatus(statusBar: vscode.StatusBarItem) {
    // Scan Generated/*.lean files for function definitions
    // Count L1corres proofs and sorry occurrences
    // This is a placeholder -- full implementation would parse lake build output
    statusBar.text = '$(shield) Clift: ready';
}

function getProofChainHtml(funcName: string): string {
    return `<!DOCTYPE html>
<html>
<head>
    <style>
        body { font-family: var(--vscode-font-family); color: var(--vscode-foreground); padding: 20px; }
        .stage { border: 1px solid var(--vscode-panel-border); border-radius: 4px; padding: 10px; margin: 8px 0; }
        .stage-name { font-weight: bold; color: var(--vscode-textLink-foreground); }
        .arrow { text-align: center; color: var(--vscode-descriptionForeground); font-size: 1.2em; }
        .verified { border-left: 3px solid #4caf50; }
        .unverified { border-left: 3px solid #f44336; }
    </style>
</head>
<body>
    <h2>Proof Chain: ${funcName}</h2>

    <div class="stage verified">
        <div class="stage-name">C Source</div>
        <code>${funcName}()</code> in <code>*.c</code>
    </div>
    <div class="arrow">| CImporter</div>

    <div class="stage verified">
        <div class="stage-name">CSimpl (Deep Embedding)</div>
        <code>${funcName}_body : CSimpl ProgramState</code>
    </div>
    <div class="arrow">| clift_l1 (SimplConv) + L1corres proof</div>

    <div class="stage verified">
        <div class="stage-name">L1 Monadic</div>
        <code>l1_${funcName}_body : L1Monad ProgramState</code>
    </div>
    <div class="arrow">| clift_l2 (LocalVarExtract) + L2corres_fwd proof</div>

    <div class="stage verified">
        <div class="stage-name">L2 Extracted</div>
        <code>l2_${funcName}_body : ... -> L1Monad Globals</code>
    </div>
    <div class="arrow">| clift_l3 (TypeStrengthen)</div>

    <div class="stage verified">
        <div class="stage-name">L3 Classified</div>
        <code>l3_${funcName}_body_level : MonadLevel</code>
    </div>
    <div class="arrow">| FuncSpec + satisfiedBy proof</div>

    <div class="stage unverified">
        <div class="stage-name">Specification</div>
        <code>${funcName}_spec : FuncSpec ProgramState</code>
    </div>
</body>
</html>`;
}
