---
id: TASK-0224
title: 'Prove heap-mutation loop functions: increment_all, replace_all, fill, reverse'
status: To Do
assignee: []
created_date: '2026-04-11 15:07'
labels:
  - sorry-elimination
  - loops
  - heap-mutation
  - ring-buffer
dependencies:
  - TASK-0222
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
These loops modify the heap on each iteration (write to node values or pointers). Harder than read-only traversals because the loop invariant must track how the heap changes. For increment_all: invariant is 'all visited nodes have val+1, all unvisited have original val'. For reverse: invariant is 'reversed prefix is a valid list, remaining suffix is a valid list'. Use L1_hoare_while with heap-aware invariant + hVal_heapUpdate_same/disjoint for each iteration.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 rb_increment_all_validHoare proven
- [ ] #2 rb_replace_all_validHoare proven
- [ ] #3 rb_fill_validHoare proven
- [ ] #4 rb_reverse_validHoare proven
<!-- AC:END -->
