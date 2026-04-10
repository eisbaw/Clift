# Clift: Lifting C into Lean 4 for Formal Verification

## Paper Outline

**Target venues**: CPP (Certified Programs and Proofs), ITP (Interactive Theorem Proving), PLDI (Programming Language Design and Implementation)

### Abstract (draft)

We present Clift, a tool for verifying C programs by lifting them into Lean 4 through a series of semantics-preserving transformations. Following the methodology of seL4's AutoCorres pipeline (originally in Isabelle/HOL), Clift parses C via clang's JSON AST, embeds it as a deeply embedded imperative language (CSimpl), and lifts it through five stages -- monadic embedding, local variable extraction, type strengthening, heap lifting, and word abstraction -- each accompanied by a machine-checked refinement proof. The result is a clean functional model on which users prove properties that chain back to the original C. We evaluate Clift on embedded systems code including ring buffers, UART drivers, hash tables, and packet parsers, and demonstrate AI-assisted proof search using Claude Code as a proof engine.

### 1. Introduction

- The verification gap: critical C code runs everywhere but remains largely unverified
- seL4's success and its Isabelle/HOL lock-in
- Why Lean 4: modern type theory, grind/omega tactics, growing AI proof ecosystem
- Contribution: first AutoCorres-style C lifting pipeline in Lean 4
- Scope: what we verify and what we do not (not a full OS kernel, but the framework for it)

### 2. Background

- 2.1 seL4 and AutoCorres: the pipeline architecture, corres refinement, trust model
- 2.2 Lean 4 as a verification platform: kernel, tactic framework, MetaM
- 2.3 Related work: CompCert (verified compiler, different goal), Aeneas (Rust -> Lean, different source language), VST (C verification in Coq, different approach), RefinedC (type-based, no lifting)
- 2.4 Why not just port AutoCorres to Lean? (Isabelle's code generation vs Lean's MetaM; SML tactics vs Lean macros)

### 3. Architecture

- 3.1 The five-stage lifting pipeline: CSimpl -> L1 (monadic) -> L2 (local extract) -> L3 (type strengthen) -> L4 (heap lift) -> L5 (word abstract)
- 3.2 CImporter: clang JSON AST to CSimpl terms (trust boundary)
- 3.3 Refinement framework: corres definition, transitivity, Hoare triple integration
- 3.4 Memory model: flat bytes -> typed split heaps (simplified Burstall-Bornat)
- 3.5 Security framework: integrity, confidentiality, availability via refinement transfer

### 4. Implementation

- 4.1 CSimpl and big-step semantics (inductive Exec relation)
- 4.2 MetaM-based lifting stages (programmatic proof construction)
- 4.3 Automation: CVcg, SepAuto, CorresAuto tactics
- 4.4 AI integration: Claude Code as proof engine for sorry elimination
- 4.5 C language coverage: integer types, structs, enums, unions, function pointers (what is and is not supported)

### 5. Evaluation

- 5.1 Test suite: 25+ C programs verified (max, gcd, swap, ring buffer, UART, hash table, etc.)
- 5.2 Proof ratios: lines of proof vs lines of C (compare to seL4's ~20:1)
- 5.3 Automation rate: percentage of proof obligations discharged automatically
- 5.4 AI proof success rate: Claude Code success/failure on proof obligations
- 5.5 Build times and scalability: how does proof checking scale with program size?
- 5.6 Comparison with AutoCorres2: what is the same, what differs, what is better/worse

### 6. Limitations and Future Work

- Current C subset restrictions (no floating point, no goto, no VLAs)
- Trust in CImporter (not verified, relies on clang)
- No concurrency model yet (single-threaded C only)
- Scaling to OS-kernel-size code (10K+ LOC)
- HeapLift maturity: simplified model vs full Tuch memory model
- Timing channels not addressed (storage channels only for security)

### Key Contributions

1. First AutoCorres-style C verification pipeline in Lean 4
2. Machine-checked refinement proofs for all five lifting stages
3. Security property framework with refinement transfer theorems
4. AI-assisted proof search integration (Claude Code as proof engine)
5. Demonstration on real embedded C code patterns

### Evaluation Plan

- **Quantitative**: LOC counts, proof ratios, build times, automation rates
- **Qualitative**: comparison with seL4/AutoCorres2, assessment of Lean 4 suitability
- **Reproducibility**: all code in the Clift repository, Nix flake for build environment
