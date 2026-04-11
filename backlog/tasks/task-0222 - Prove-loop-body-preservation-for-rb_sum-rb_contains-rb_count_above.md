---
id: TASK-0222
title: 'Prove loop body preservation for rb_sum, rb_contains, rb_count_above'
status: To Do
assignee: []
created_date: '2026-04-11 15:07'
labels:
  - sorry-elimination
  - loops
  - ring-buffer
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
These loop functions follow the same pattern: traverse linked list, accumulate result. The loop invariant (LinkedListValid) is defined. L1_hoare_while is proven. The blocker is proving body preservation through the kernel depth limit. Strategy: (1) define the while body's modify function as an explicit named def with anonymous constructors, (2) prove projection lemmas with [local irreducible], (3) apply L1_hoare_guard_modify_fused for each guard+modify in the body, (4) compose with L1_hoare_seq. The rb_count_nodes proof (already done) is the template — adapt it for these 3 functions.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 rb_sum_validHoare proven
- [ ] #2 rb_contains_validHoare proven
- [ ] #3 rb_count_above_validHoare proven
- [ ] #4 Each follows rb_count_nodes proof pattern
<!-- AC:END -->
