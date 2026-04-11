---
id: TASK-0227
title: Close RBExtRefinement sorry after all validHoare proofs complete
status: To Do
assignee: []
created_date: '2026-04-11 15:07'
labels:
  - sorry-elimination
  - refinement
  - milestone
dependencies:
  - TASK-0225
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
RBExtRefinement.lean has 1 sorry in ring_buffer_ext_refines_queue_spec, transitively blocked on the 25 validHoare sorry in RBExtFuncSpecs.lean. Once all validHoare are proven (tasks 0220-0225), this should close automatically — the refinement theorem just composes the per-function proofs.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 ring_buffer_ext_refines_queue_spec proven with zero sorry
- [ ] #2 #print axioms shows only propext/Quot.sound/Classical.choice
<!-- AC:END -->
