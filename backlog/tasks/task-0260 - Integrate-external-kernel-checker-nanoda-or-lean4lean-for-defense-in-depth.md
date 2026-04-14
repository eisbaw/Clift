---
id: TASK-0260
title: Integrate external kernel checker (nanoda or lean4lean) for defense-in-depth
status: To Do
assignee: []
created_date: '2026-04-14 18:40'
labels:
  - credibility
  - infrastructure
dependencies: []
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The Lean Kernel Arena demonstrated that running MULTIPLE independent kernel implementations catches real bugs — nanoda (Rust) found an arithmetic bug in the official Lean 4 kernel in 2022 that the C++ kernel missed.

Defense-in-depth: verify our proofs with at least 2 independent checkers.

Options:
1. nanoda_lib (Rust): independent reimplementation, ~5000 LOC. Build from source via cargo.
2. Lean4Lean: Lean typechecker written in Lean itself. 20-50% slower but catches different bugs.
3. The Comparator tool (official) orchestrates multiple checkers in sandboxes.

Integration:
1. Export proofs: lean4export to produce export files
2. Run nanoda on export files
3. Run Lean4Lean on export files
4. Compare results — any disagreement is a bug in one checker

This is the gold standard for proof assurance — seL4 doesn't have this (Isabelle has only one kernel).

Reference: https://github.com/ammkrn/nanoda_lib
Reference: https://github.com/leanprover/lean4lean
Reference: https://arena.lean-lang.org/
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 At least one external checker integrated
- [ ] #2 Export files generated for all Clift/ theorems
- [ ] #3 External checker passes on all exported proofs
- [ ] #4 CI job for external verification
<!-- AC:END -->
