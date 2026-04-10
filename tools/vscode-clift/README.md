# Clift VS Code Extension

Inline verification feedback for C code verified with the Clift pipeline.

## What It Does

This extension integrates with the Lean 4 LSP to show verification status
for C functions going through the Clift pipeline:

1. **Gutter Icons**: Green/yellow/red icons on function definitions showing
   verification status (verified / partially verified / unverified).

2. **Sorry Highlighting**: Unproven obligations are highlighted with squiggly
   underlines and grouped in the Problems panel.

3. **Prove with AI**: Right-click on a `sorry` to invoke the Claude proof
   engine, which attempts to fill in the proof automatically.

4. **Proof Chain Visualization**: See the full transformation chain from C
   source through CSimpl, L1, L2, L3 to the abstract specification.

5. **CImporter Integration**: Import C files directly from the editor,
   running clang and the CImporter pipeline.

## Prerequisites

- [Lean 4 VS Code extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
- Nix shell with `clang`, `python3`, `lake` (from the Clift project's flake)
- `clift-prove-by-claudecode` in PATH (for AI proof feature)

## How It Works

The extension does NOT replace the Lean 4 LSP. It runs alongside it,
reading Lean's diagnostic output to determine verification status.

### Verification Status Detection

For each function `f` in `Generated/<Module>.lean`:

| Status | Condition |
|--------|-----------|
| Verified (green) | L1corres proof exists, FuncSpec satisfied, no sorry |
| Partial (yellow) | L1corres proof exists but FuncSpec incomplete or missing |
| Unverified (red) | No L1corres proof or build error |

### Integration Points

- **Lean LSP**: reads diagnostics (errors, sorry warnings)
- **CImporter**: runs Python importer on C files
- **lake**: triggers builds and reads output
- **clift-prove-by-claudecode**: AI proof engine

## Configuration

| Setting | Default | Description |
|---------|---------|-------------|
| `clift.projectRoot` | (auto) | Root directory of Clift project |
| `clift.pythonPath` | `python3` | Python interpreter for CImporter |
| `clift.autoVerifyOnSave` | `false` | Re-verify on .lean file save |
| `clift.proofEngine` | `claudecode` | AI proof backend |

## Development

```bash
# Enter Clift nix shell
nix develop

# Install dependencies
cd tools/vscode-clift
npm install

# Compile
npm run compile

# Launch extension host for testing
# Press F5 in VS Code with this folder open
```

## Architecture

See `spec.md` for detailed specification.

```
Extension
  +-- VerificationStatusProvider  (gutter icons + status bar)
  +-- ProofChainProvider          (webview panel)
  +-- AIProofCodeAction           (code action + command)
  +-- CImporterIntegration        (file watcher + command)
```
