---
name: Clift project status and architecture
description: Clift lifts C into Lean 4 for formal verification, replicating seL4's AutoCorres pipeline. Zero sorry, 78 tasks completed, 6 ADRs.
type: project
---

Clift is a tool that lifts C code into Lean 4 for formal verification, following seL4's AutoCorres methodology.

**Why:** Verify the actual C that runs (not a rewrite). seL4's AutoCorres is Isabelle-only; Clift brings it to Lean 4 for AI ecosystem access.

**How to apply:** Read plan.md for full architecture. Key pipeline: C → clang JSON → CImporter (Python) → CSimpl (deep embedding) → L1 (NondetM monad) → L3 (type strengthening) → L5 (word abstraction) → user proofs.

Status as of 2026-04-09: Phases 0-4 complete. Zero sorry, zero axioms. 6,776 LOC Lean + 2,638 LOC Python. 6 ADRs. Mathlib dropped (builds use <500MB). Key proofs: gcd_correct_nat (Nat→Nat→Nat, full chain to C), swap_correct (pointer exchange with frame reasoning).
