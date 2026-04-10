# Clift VS Code Extension Specification

## Overview

The Clift VS Code extension provides inline verification feedback for C code
verified through the Clift pipeline (C -> CSimpl -> L1 -> L2 -> L3 -> Spec).
It integrates with the Lean 4 LSP and the CImporter to give developers
real-time visibility into verification status.

## Architecture

```
VS Code Editor
    |
    +-- Lean 4 LSP (existing) -- provides type info, error diagnostics
    |
    +-- Clift Extension (this)
         |
         +-- Verification Status Provider
         |     Reads Lean build output, classifies functions as:
         |     - verified (green): L1corres proof + FuncSpec satisfied, no sorry
         |     - partial (yellow): L1corres proof exists but FuncSpec has sorry
         |     - unverified (red): no L1corres proof or build error
         |
         +-- Proof Chain Visualizer
         |     For a given function, shows the chain:
         |     C source -> CSimpl body -> L1 monadic -> L2 extracted -> spec
         |
         +-- AI Proof Action
         |     Invokes clift-prove-by-claudecode on selected sorry
         |
         +-- CImporter Integration
               Runs CImporter on .c files, regenerates .lean
```

## Feature 1: Verification Status Gutter Icons

### Data Source

The extension scans the workspace for:
1. `Generated/*.lean` files -- each contains `*_body : CSimpl ProgramState` defs
2. Build output from `lake build` -- errors indicate unverified functions
3. `#print axioms` output -- presence of `sorry` axiom means incomplete proof

### Classification Algorithm

For each function `f` found in `Generated/<Module>.lean`:

1. Check if `<Module>.l1_<f>_body_corres` exists (L1corres proof)
   - If not: status = UNVERIFIED (red)
2. Check if `<Module>.l1_<f>_body_corres` uses `sorry` axiom
   - If yes: status = PARTIAL (yellow)
3. Check if a `FuncSpec` and `satisfiedBy` proof exist
   - If yes and no sorry: status = VERIFIED (green)
   - If yes with sorry: status = PARTIAL (yellow)
   - If no FuncSpec: status = PARTIAL (yellow, lifted but unspecified)

### Display

- Gutter icon on the `def <f>_body` line in Generated .lean files
- Gutter icon on the function definition in the original .c file (if open)
- Status bar: "Clift: 15/40 verified, 10 partial, 15 unverified"
- Hover tooltip shows: verification level, sorry count, proof chain summary

## Feature 2: Unproven Obligation Highlighting

### Data Source

Parse Lean LSP diagnostics for:
- `sorry` warnings (Lean reports these as warnings)
- `axiom` declarations that indicate incomplete proofs
- Build errors in proof files

### Display

- Red squiggly underline on `sorry` terms
- Yellow squiggly on axiom-based proofs
- Problems panel integration: group by function, show obligation type

## Feature 3: "Prove with AI" Code Action

### Trigger

- Code action on `sorry` terms (lightbulb icon)
- Right-click context menu on any sorry
- Command palette: "Clift: Prove with AI"

### Workflow

1. Extract the sorry's goal context (from Lean LSP hover info)
2. Invoke `clift-prove-by-claudecode` with the file and line number
3. Show progress notification: "Proving obligation at line 42..."
4. On success: replace sorry with generated proof term
5. On failure: show notification with explanation

### Configuration

- `clift.proofEngine`: which backend to use (claudecode or none)
- Timeout: 120 seconds per sorry (configurable)
- Batch mode: attempt all sorrys in a file sequentially

## Feature 4: Proof Chain Visualization

### Trigger

- Command: "Clift: Show Proof Chain"
- Click on a verified function's gutter icon

### Display

A webview panel showing the transformation chain:

```
[C source]           uint32_t gcd(uint32_t a, uint32_t b) { ... }
    | CImporter
    v
[CSimpl]             gcd_body : CSimpl ProgramState
    | clift_l1 (SimplConv)
    v
[L1 Monadic]         l1_gcd_body : L1Monad ProgramState
    | L1corres proof: l1_gcd_body_corres
    | clift_l2 (LocalVarExtract)
    v
[L2 Extracted]       l2_gcd_body : UInt32 -> UInt32 -> L1Monad Globals
    | L2corres_fwd proof
    | clift_l3 (TypeStrengthen)
    v
[L3 Classified]      level = pure
    |
    v
[FuncSpec]           gcd_spec : FuncSpec ProgramState
    | satisfiedBy proof
    v
[Abstract Spec]      GCD specification over Nat
    | refinement proof
    v
[Properties]         gcd_correct: gcd a b = Nat.gcd a b
```

Each node is clickable and jumps to the corresponding definition in the editor.

## Feature 5: CImporter Integration

### Trigger

- Command: "Clift: Import C File" (from .c file context)
- File watcher: auto-reimport on .c file save (opt-in)

### Workflow

1. Run `clang -Xclang -ast-dump=json -fsyntax-only <file>`
2. Run `python3 CImporter/import.py <json> -o Generated/<Name>.lean`
3. Show diff of generated .lean file
4. Trigger `lake build` for the generated module

## Integration with Lean 4 LSP

The extension does NOT replace or wrap the Lean 4 LSP. It runs alongside it:

- Lean 4 LSP handles: syntax highlighting, type checking, go-to-definition,
  error reporting, completion, hover info
- Clift extension adds: verification status overlay, proof chain view,
  AI proof action, CImporter workflow

The extension reads from the Lean LSP's diagnostic output to determine
which functions have errors/warnings (sorry).

## File Layout

```
tools/vscode-clift/
  package.json          -- extension manifest
  tsconfig.json         -- TypeScript config
  spec.md               -- this file
  README.md             -- user-facing docs
  src/
    extension.ts        -- entry point: activate/deactivate
    verificationStatus.ts  -- gutter icon provider
    proofChain.ts       -- proof chain webview
    aiProof.ts          -- AI proof code action
    cimporter.ts        -- CImporter integration
    config.ts           -- configuration management
```

## Non-Goals (v0.1)

- Custom Lean LSP features (hover, completion) -- use standard Lean 4 extension
- Proof editing UI -- users write proofs in normal Lean files
- CImporter AST visualization -- too complex for v0.1
- Multi-project support -- single lakefile.lean per workspace
- Remote verification server -- everything runs locally

## Dependencies

- VS Code 1.85+
- Lean 4 extension (lean4) installed and configured
- Nix shell with clang, python3, lake available
- clift-prove-by-claudecode in PATH (for AI proof feature)

## Future Work (v0.2+)

- Verification coverage report (HTML/markdown)
- Integration with CI: show CI verification status in editor
- Proof replay: step through proof chain interactively
- Multi-file C project support (auto-detect compilation units)
- Incremental re-verification (only re-check changed functions)
