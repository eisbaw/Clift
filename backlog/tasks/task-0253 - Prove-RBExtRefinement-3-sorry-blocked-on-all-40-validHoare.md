---
id: TASK-0253
title: 'Prove RBExtRefinement (3 sorry, blocked on all 40 validHoare)'
status: To Do
assignee: []
created_date: '2026-04-14 07:02'
labels:
  - sorry-elimination
  - refinement
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
3 sorry in RBExtRefinement.lean (lines 507, 520, 550). ALL blocked on rb_drain_to being proven (the last ring buffer validHoare).

ring_buffer_ext_refines_queue_spec (line 507): needs all 40 validHoare + refinement glue.
rb_ext_inv_preserved (line 520): needs ring_buffer_ext_refines_queue_spec.
transfer theorem (line 550): needs ring_buffer_ext_refines_queue_spec + queue_push_pop_empty.

Once drain_to is proven (40/40 validHoare), these 3 may be closeable with the existing AbstractSpec + GlobalInvariant infrastructure.

Estimated: ~100 lines once unblocked.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 ring_buffer_ext_refines_queue_spec proven
- [ ] #2 rb_ext_inv_preserved proven
- [ ] #3 transfer theorem proven
- [ ] #4 RBExtRefinement.lean fully sorry-free
<!-- AC:END -->
