---
id: TASK-0251
title: Prove PQ pq_swap non-failure (foundation for pq_bubble_up/down)
status: Done
assignee:
  - '@claude'
created_date: '2026-04-14 07:02'
updated_date: '2026-04-15 02:14'
labels:
  - sorry-elimination
  - priority-queue
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
pq_swap is the innermost callee in the PQ call chain: pq_insert→pq_bubble_up→pq_swap. It swaps two array elements. Pattern C (guard+modify chain).

Currently pq_swap_ok_hoare in PriorityQueueProof.lean has sorry in the body (catch handler proven, body non-failure not). Need to prove the guard chain through 2 heapUpdates (swap data[i] and data[j]).

Precondition: dataArrayValid (all array elements valid). Guards check heapPtrValid data[i] and data[j].

Template: ht_lookup h_body_nf in HashTableProof.lean (guard chain through array access).

Estimated: ~50 lines. Once proven, enables pq_bubble_up and pq_bubble_down proofs.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 pq_swap_ok_hoare proven (0 sorry)
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Proved pq_swap_ok_hoare by decomposing the L1 body into named step functions with anonymous constructors (16-field Locals struct requires this to avoid kernel deep recursion). Used L1_guard_modify_result and L1_guard_guard_modify_result to prove each guard passes, then L1_seq_singleton_ok to chain them. heapPtrValid preservation through heapUpdate proven via projection lemmas and heapUpdate_preserves_heapPtrValid.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Proved pq_swap_ok_hoare (pq_swap non-failure): eliminated 1 sorry.

Pattern: decompose L1 body into named step functions with anonymous constructors to avoid kernel deep recursion on 16-field Locals struct. Prove each guard passes via L1_guard_modify_result / L1_guard_guard_modify_result, chain via L1_seq_singleton_ok, wrap with L1_catch_singleton_ok.

Sorry count in PriorityQueueProof.lean: 5 -> 4.
<!-- SECTION:FINAL_SUMMARY:END -->
