---
id: TASK-0189
title: >-
  Eliminate 32 sorry in RBExtFuncSpecs.lean (ring buffer validHoare/totalHoare
  proofs)
status: To Do
assignee: []
created_date: '2026-04-10 20:49'
labels:
  - sorry-elimination
  - ring-buffer
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
RBExtFuncSpecs.lean has 25 validHoare sorry and 7 totalHoare sorry for ring_buffer_ext functions. Specs are fully defined, proofs are stubbed. This is the single largest sorry cluster and blocks RBExtRefinement (3 more sorry). Priority order from SorryAudit: simple accessors first (rb_capacity, rb_size, rb_remaining, rb_is_empty, rb_is_full, rb_stats_total_ops, rb_iter_has_next), then push/pop/init.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 25 validHoare sorry eliminated
- [ ] #2 7 totalHoare sorry eliminated
- [ ] #3 All proofs kernel-checked (lake build passes)
<!-- AC:END -->
