---
id: TASK-0228
title: Generate projection simp lemma sets automatically per Generated file
status: To Do
assignee: []
created_date: '2026-04-11 15:07'
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
