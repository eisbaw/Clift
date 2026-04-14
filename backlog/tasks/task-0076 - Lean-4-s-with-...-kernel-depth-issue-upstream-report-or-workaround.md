---
id: TASK-0076
title: 'Lean 4 { s with ... } kernel depth issue: upstream report or workaround'
status: To Do
assignee:
  - '@mped'
created_date: '2026-04-09 19:34'
updated_date: '2026-04-14 22:12'
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

Issue documented: Lean 4 kernel deep recursion on nested structure projections through composed functions. Affects any proof composing 7+ state transformations with CState/Globals. Minimal reproducer needed. Workaround exists: SwapHeapLift.lean proofs bypass the issue.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Lean 4 kernel depth issue: documented and workaround found.

Root cause: The kernel has a hardcoded recursion depth limit. When checking rfl proofs like (swap_f1 s).globals = s.globals, the kernel type-checks the entire anonymous constructor including hVal s.globals.rawHeap s.locals.a, which unfolds through MemType.fromMem -> UInt32.fromBytes' -> assembleByte -> UInt8/BitVec arithmetic, exceeding the depth limit.

Workaround: Mark hVal and heapUpdate as [local irreducible] before proofs that involve structure projection through composed state functions. Use simp with explicit projection lemmas to rewrite state fields before heapPtrValid/hVal see composed functions.

No upstream issue filed — the workaround is clean and general.
<!-- SECTION:FINAL_SUMMARY:END -->
