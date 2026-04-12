---
id: TASK-0190
title: Eliminate 3 sorry in RBExtRefinement.lean (refinement proofs)
status: To Do
assignee: []
created_date: '2026-04-10 20:49'
updated_date: '2026-04-11 22:35'
labels:
  - sorry-elimination
  - ring-buffer
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
3 sorry in ring_buffer_ext_refines_queue_spec, rb_ext_inv_preserved, and transfer theorem. All transitively blocked on RBExtFuncSpecs validHoare proofs being completed first.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 ring_buffer_ext_refines_queue_spec proven
- [ ] #2 rb_ext_inv_preserved proven
- [ ] #3 Transfer theorem proven
- [ ] #4 All proofs kernel-checked
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
2026-04-12: Updated count. 12/40 validHoare now proven (was "only 4"). Still blocked on remaining 19 sorry in RBExtFuncSpecs.lean.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Not achievable this session. All 3 sorry in RBExtRefinement.lean are transitively blocked on the 25 validHoare sorry in RBExtFuncSpecs.lean. ring_buffer_ext_refines_queue_spec requires all 40 validHoare proofs. Only 4 of 40 are proven. The remaining 25 sorry need loop invariants, multi-heap projection lemma suites, and inter-procedural spec composition -- each 50-300 lines of proof infrastructure per function.
<!-- SECTION:FINAL_SUMMARY:END -->
