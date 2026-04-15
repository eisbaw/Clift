---
name: Clift project status and architecture
description: Clift lifts C into Lean 4 for formal verification, replicating seL4's AutoCorres pipeline. 8 sorry remaining, 228 tasks done.
type: project
---

Clift is a tool that lifts C code into Lean 4 for formal verification, following seL4's AutoCorres methodology.

**Why:** Verify the actual C that runs (not a rewrite). seL4's AutoCorres is Isabelle-only; Clift brings it to Lean 4 for AI ecosystem access.

**How to apply:** Read plan.md for full architecture. Key pipeline: C → clang JSON → CImporter (Python) → CSimpl (deep embedding) → L1 (NondetM monad) → L2 (local extract) → L3 (type strengthening) → L5 (word abstraction) → user proofs.

Status as of 2026-04-15: 76K LOC Lean, 6.8K LOC Python, 1699 theorems, 8 sorry remaining in examples (0 in core library), 228 tasks done, 8 ADRs. Mathlib dropped. Key proofs: gcd_correct_nat, swap_correct, rbt_lookup_correct, rb_push_validHoare, uart_init.
