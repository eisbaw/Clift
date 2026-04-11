---
id: TASK-0228
title: Generate projection simp lemma sets automatically per Generated file
status: To Do
assignee: []
created_date: '2026-04-11 15:07'
updated_date: '2026-04-11 21:27'
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
- [ ] #1 Auto-generation tool produces correct projection lemmas for SwapProof
- [ ] #2 Auto-generation tool produces correct projection lemmas for RBExtFuncSpecs
- [ ] #3 All generated lemmas are rfl proofs with [local irreducible] hVal heapUpdate
- [ ] #4 Projection lemma file importable by proof files
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
