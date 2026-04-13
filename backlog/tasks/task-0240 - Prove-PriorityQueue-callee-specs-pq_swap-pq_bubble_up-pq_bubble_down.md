---
id: TASK-0240
title: 'Prove PriorityQueue callee specs (pq_swap, pq_bubble_up, pq_bubble_down)'
status: To Do
assignee: []
created_date: '2026-04-13 09:53'
labels:
  - sorry-elimination
  - inter-procedural
  - priority-queue
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
2 sorry in PriorityQueueProof.lean: pq_insert (calls pq_bubble_up) and pq_extract_min (calls pq_bubble_down). Both blocked on callee specs.

DEPENDENCY CHAIN:
pq_insert → calls pq_bubble_up → which calls pq_swap (in a while loop)
pq_extract_min → calls pq_bubble_down → which calls pq_swap (in a while loop)

NEEDED:
1. Prove pq_swap_validHoare (array element swap — guard+modify chain)
2. Prove pq_bubble_up_validHoare (while loop calling pq_swap via dynCom)
3. Prove pq_bubble_down_validHoare (while loop calling pq_swap via dynCom)
4. Then prove pq_insert and pq_extract_min using L1_hoare_dynCom_call

Infrastructure exists: L1_hoare_dynCom_call, L1ProcEnv lookup lemmas (already in PriorityQueueProof.lean), dataArrayValid predicate.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 pq_swap_validHoare proven
- [ ] #2 pq_bubble_up_validHoare proven
- [ ] #3 pq_bubble_down_validHoare proven
- [ ] #4 pq_insert_correct proven
- [ ] #5 pq_extract_min_correct proven
<!-- AC:END -->
