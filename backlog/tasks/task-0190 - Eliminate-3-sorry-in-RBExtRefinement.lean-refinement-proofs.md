---
id: TASK-0190
title: Eliminate 3 sorry in RBExtRefinement.lean (refinement proofs)
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
3 sorry in ring_buffer_ext_refines_queue_spec, rb_ext_inv_preserved, and transfer theorem. All transitively blocked on RBExtFuncSpecs validHoare proofs being completed first.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 ring_buffer_ext_refines_queue_spec proven
- [ ] #2 rb_ext_inv_preserved proven
- [ ] #3 Transfer theorem proven
- [ ] #4 All proofs kernel-checked
<!-- AC:END -->
