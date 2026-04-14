---
id: TASK-0251
title: Prove PQ pq_swap non-failure (foundation for pq_bubble_up/down)
status: To Do
assignee: []
created_date: '2026-04-14 07:02'
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
- [ ] #1 pq_swap_ok_hoare proven (0 sorry)
<!-- AC:END -->
