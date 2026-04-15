---
id: TASK-0252
title: >-
  Prove pq_bubble_up and pq_bubble_down non-failure (while loop + dynCom
  pq_swap)
status: In Progress
assignee:
  - '@claude'
created_date: '2026-04-14 07:02'
updated_date: '2026-04-15 02:59'
labels:
  - sorry-elimination
  - priority-queue
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Depends on: pq_swap_ok_hoare proven first.

pq_bubble_up: while loop calling pq_swap via dynCom. Pattern D+E. Need loop invariant (dataArrayValid + index bounds). Each iteration swaps parent/child, advances index upward.

pq_bubble_down: similar but advances downward with min-child selection.

Once proven, these enable pq_insert_correct and pq_extract_min_correct via L1_hoare_dynCom_call.

Estimated: ~150 lines each. Template: the proven ht_insert while loop body in HashTableProof.lean.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 pq_bubble_up_ok_hoare proven
- [ ] #2 pq_bubble_down_ok_hoare proven
- [ ] #3 pq_insert_correct proven (0 sorry)
- [ ] #4 pq_extract_min_correct proven (0 sorry)
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Proved pq_bubble_up_ok_hoare (while loop + dynCom pq_swap call).
- Added pq_swap_preserves_hpv: stronger swap spec preserving all heapPtrValid
- Added UInt32 arithmetic lemmas for parent index bound
- NondetM-level reasoning for dynCom+call resolution
- Sorry count: 4 -> 2 (pq_insert_correct 2 sorry, pq_extract_min_correct 1 sorry)
- pq_bubble_down not attempted (requires similar while loop + dynCom proof)

Attempted pq_insert dynCom(bubble_up)+rest proof but hit kernel deep recursion (16-field Locals struct). Would need step function decomposition with anonymous constructors for all modify operations. The proof approach is correct (resolve L1.call via simp, use pq_bubble_up_ok_hoare for callee spec) but the mechanical refactoring is too large for this session.

Final sorry count: 4 -> 2
- pq_bubble_up_ok_hoare: PROVEN (while loop + dynCom pq_swap)
- pq_insert guard+modify: PROVEN (heapUpdate disjointness)
- pq_insert dynCom(bubble_up)+rest: BLOCKED on kernel depth (16-field struct)
- pq_extract_min: BLOCKED (depends on unproven pq_bubble_down)
<!-- SECTION:NOTES:END -->
