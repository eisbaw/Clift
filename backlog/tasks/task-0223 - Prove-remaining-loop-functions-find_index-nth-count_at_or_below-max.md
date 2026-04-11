---
id: TASK-0223
title: 'Prove remaining loop functions: find_index, nth, count_at_or_below, max'
status: To Do
assignee: []
created_date: '2026-04-11 15:07'
labels:
  - sorry-elimination
  - loops
  - ring-buffer
dependencies:
  - TASK-0222
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Same pattern as task-0222 but with additional complexity: rb_nth has conditional inside loop body, rb_max has heap write per iteration, rb_find_index tracks index. Each needs a slightly different loop invariant extending LinkedListValid with the accumulator state. The L1_hoare_while + L1_hoare_condition combination handles conditionals inside loops.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 rb_find_index_validHoare proven
- [ ] #2 rb_nth_validHoare proven
- [ ] #3 rb_count_at_or_below_validHoare proven
- [ ] #4 rb_max_validHoare proven
<!-- AC:END -->
