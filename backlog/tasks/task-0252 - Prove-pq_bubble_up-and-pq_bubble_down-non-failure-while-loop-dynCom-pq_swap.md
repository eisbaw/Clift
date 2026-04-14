---
id: TASK-0252
title: >-
  Prove pq_bubble_up and pq_bubble_down non-failure (while loop + dynCom
  pq_swap)
status: To Do
assignee: []
created_date: '2026-04-14 07:02'
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
