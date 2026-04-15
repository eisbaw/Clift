---
id: TASK-0228
title: Generate projection simp lemma sets automatically per Generated file
status: Done
assignee:
  - '@claude'
created_date: '2026-04-11 15:07'
updated_date: '2026-04-15 06:04'
labels:
  - automation
  - sorry-elimination
  - infrastructure
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Each sorry elimination requires per-function projection lemmas like '(f s).globals = s.globals := rfl'. Currently hand-written. Automate: for each L1.modify lambda in a Generated file, produce the full set of projection lemmas. Use CImporter/proof_engine/gen_projections.py (already exists) or a Lean MetaM that inspects the modify lambda body. The output is a .lean file with @[simp] theorems that can be imported by proof files. This removes the biggest manual effort from sorry elimination.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Auto-generation tool produces correct projection lemmas for SwapProof
- [x] #2 Auto-generation tool produces correct projection lemmas for RBExtFuncSpecs
- [x] #3 All generated lemmas are rfl proofs with [local irreducible] hVal heapUpdate
- [x] #4 Projection lemma file importable by proof files
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
The two-step projection pattern is THE key:
1. Prove step_fn_locals_eq : (step_fn s).locals = ⟨f1, ..., fN⟩ via unfold step_fn; rfl
2. Prove step_fn_field : (step_fn s).locals.field = value via rw [step_fn_locals_eq]

For anonymous constructors: step_fn s = ⟨s.globals, ⟨new_field1, ..., new_fieldN⟩⟩
The _locals_eq proof works because CState.mk.locals reduces in one iota step.
The _field proof works because rw replaces .locals with the known constructor, making .field shallow.

This needs to be auto-generated for each L1.modify lambda. gen_projections.py exists but needs updating for this two-step approach.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Implemented auto-generation of projection simp lemma sets from Generated/*.lean files.

Changes:
- Rewrote CImporter/proof_engine/gen_projections.py to read Generated files directly (Locals struct + .basic lambdas) instead of requiring hand-written step functions
- Generates: noncomputable step functions with anonymous constructors, two-step projection lemmas (locals_eq/globals_eq + per-field @[simp]), funext theorems
- Handles both locals-only updates and globals (heap) updates
- Supports --func-prefix filter for generating subsets
- Added Generated/SwapProjections.lean (3 steps, 3 fields) - builds in 659ms
- Added Generated/RingBufferExtProjections.lean (213 steps, 46 fields, 24K lines) - builds in 23s
- Added 18 Python tests in CImporter/tests/test_gen_projections.py
- Added just gen-projections and just gen-projections-all recipes
- Updated lakefile.lean with new Generated roots

Limitations:
- Inter-procedural call lambdas using saved.locals are skipped (5 warnings on RBExt)
- Does not generate for functions without _body suffix
<!-- SECTION:FINAL_SUMMARY:END -->
