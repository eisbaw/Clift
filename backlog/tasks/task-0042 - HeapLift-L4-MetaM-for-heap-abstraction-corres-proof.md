---
id: TASK-0042
title: 'HeapLift (L4): MetaM for heap abstraction + corres proof'
status: To Do
assignee:
  - '@mped'
created_date: '2026-04-08 21:38'
updated_date: '2026-04-14 22:12'
labels:
  - phase-3c
  - lifting
  - metam
dependencies:
  - TASK-0041
references:
  - ext/AutoCorres2/heap_lift.ML
  - ext/AutoCorres2/HeapLift.thy
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Write MetaM that transforms L3 functions by replacing raw heap operations (hVal, heapUpdate) with typed heap operations (simpleLift, typed write). Generate HLcorres proof relating raw and typed heap states. Study heap_lift.ML.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 MetaM rewrites hVal calls to simpleLift calls
- [ ] #2 MetaM rewrites heapUpdate calls to typed heap writes
- [ ] #3 HLcorres proof generated for each function
- [x] #4 swap.c lifts through HeapLift correctly
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Phase 3 plan calls for manual HeapLift corres, not MetaM automation. Implemented SwapHeapLift.lean with manual proofs. MetaM automation deferred to Phase 4.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Manual HeapLift correspondence for swap in Examples/SwapHeapLift.lean. Proves: swap_heapLift_corres (raw swap satisfies sep-logic spec), swap_heapLift_frame (disjoint pointers preserved), swap_simpleLift_a/b (simpleLift readback). All proofs sorry-free, standard axioms only. MetaM rewriting (AC 1-3) deferred to Phase 4 per plan.
<!-- SECTION:FINAL_SUMMARY:END -->
