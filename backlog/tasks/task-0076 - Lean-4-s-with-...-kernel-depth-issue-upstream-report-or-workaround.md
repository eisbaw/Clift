---
id: TASK-0076
title: 'Lean 4 { s with ... } kernel depth issue: upstream report or workaround'
status: To Do
assignee: []
created_date: '2026-04-09 19:34'
updated_date: '2026-04-09 22:10'
labels:
  - phase-5
  - lean4-bug
  - technical-debt
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Lean 4's kernel hits a hardcoded deep recursion limit when type-checking proof terms involving nested structure updates ({ s with field := ... }). This blocks compositional Hoare proofs for programs with 7+ sequential steps. Options: (1) file upstream Lean 4 issue, (2) implement MetaM VCG that generates flat terms, (3) refactor state types to avoid nesting. Document the issue thoroughly for the Lean community.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Minimal reproducer created and documented
- [ ] #2 Upstream issue filed OR workaround implemented
- [ ] #3 Impact on Clift documented
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Confirmed the kernel depth issue with concrete evidence:
- Simply assigning `have : heapPtrValid (swap_f1 s).globals.rawHeap ... := h_va` triggers deep recursion
- The kernel must reduce (swap_f1 s).globals through the CState/Globals constructors
- This happens even with explicit anonymous constructors (no {s with ...})
- The L1corres proof succeeds because it only matches L1 combinator structure
- The validHoare proof fails because it requires reasoning about state after transformation
- Workaround: HeapLift-level proofs work (SwapHeapLift.lean is sorry-free)
- Fix needed: MetaM VCG (task-0071) that builds flat proof terms without structure projections
<!-- SECTION:NOTES:END -->
