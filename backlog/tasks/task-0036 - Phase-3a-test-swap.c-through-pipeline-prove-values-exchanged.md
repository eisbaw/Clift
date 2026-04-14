---
id: TASK-0036
title: 'Phase 3a test: swap.c through pipeline, prove values exchanged'
status: To Do
assignee:
  - '@mped'
created_date: '2026-04-08 21:38'
updated_date: '2026-04-14 22:12'
labels:
  - phase-3a
  - test
  - milestone
dependencies:
  - TASK-0035
  - TASK-0030
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Run swap.c through the full pipeline (CImporter -> L1 -> L2 -> L3 -> L5). Prove that after swap(&a, &b), *a and *b are exchanged. This is the first pointer verification test.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 swap.c imports, lifts through L1-L2-L3-L5
- [ ] #2 theorem swap_correct proven: *a and *b exchanged
- [x] #3 Proof handles pointer validity preconditions
- [ ] #4 No sorry in proof
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Create Examples/SwapProof.lean
2. Define L1 version of swap_body
3. Prove L1corres for swap
4. Prove swap_correct: after swap, *a and *b are exchanged
5. Handle pointer validity preconditions
6. Add to lakefile, lake build
7. Verify no sorry
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
L1corres for swap is sorry-free. swap_values_exchanged (the heap property) is sorry-free. The one remaining sorry is in l1_swap_validHoare which requires mechanical set membership reasoning through the L1 monadic computation. This is the same pattern as gcd but more verbose due to heap guards. Filing follow-up task.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Phase 3a swap test: partial completion.

Completed:
- swap.c imports through CImporter -> Generated/Swap.lean compiles
- L1 monadic version (l1_swap_body) defined with guard+modify structure
- L1corres proof complete and sorry-free
- swap_values_exchanged theorem proven: hVal/heapUpdate disjoint reasoning works
- Full pipeline architecture: L1corres_cHoare_bridge connects L1 to CSimpl

Remaining (filed as task-0062):
- l1_swap_validHoare has one sorry: mechanical L1 monadic set membership reasoning
- This is needed for the final swap_correct to be sorry-free

The sorry is NOT in any heap reasoning or corres proof -- it is purely in the mechanical tracing through L1.seq/L1.guard/L1.modify result sets. The c_vcg tactic (Phase 4) should automate this.
<!-- SECTION:FINAL_SUMMARY:END -->
