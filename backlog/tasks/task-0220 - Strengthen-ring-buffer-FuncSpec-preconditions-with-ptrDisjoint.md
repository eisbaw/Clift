---
id: TASK-0220
title: Strengthen ring buffer FuncSpec preconditions with ptrDisjoint
status: To Do
assignee: []
created_date: '2026-04-11 15:06'
updated_date: '2026-04-11 21:27'
labels:
  - sorry-elimination
  - preconditions
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
rb_push, rb_pop, rb_swap_front_back, rb_iter_next sorry are blocked because after heapUpdate to a node pointer, guards reference hVal through the updated heap. hVal_heapUpdate_disjoint requires ptrDisjoint which is missing from the specs. Add ptrDisjoint(head, rb), ptrDisjoint(tail, rb), and ptrDisjoint(node, rb) to preconditions of all heap-mutating functions. This is semantically correct — the ring buffer struct and its nodes are at different heap locations.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 rb_push_spec.pre includes ptrDisjoint for rb vs node pointers
- [ ] #2 rb_pop_spec.pre includes ptrDisjoint
- [ ] #3 rb_swap_front_back_spec.pre includes ptrDisjoint for head/tail vs rb
- [ ] #4 rb_iter_next_spec.pre includes ptrDisjoint
- [ ] #5 All specs still compile after changes
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Confirmed needed: rb_push, rb_pop, rb_swap_front_back, rb_iter_next all need ptrDisjoint in preconditions. After heapUpdate to node pointer, guards reference hVal through updated heap. hVal_heapUpdate_disjoint requires ptrDisjoint.

Also: rb_contains, rb_count_above, rb_sum need LinkedListValid in preconditions (already added for rb_count_nodes and rb_sum).
<!-- SECTION:NOTES:END -->
