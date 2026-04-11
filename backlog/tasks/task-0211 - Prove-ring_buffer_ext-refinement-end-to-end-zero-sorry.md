---
id: TASK-0211
title: Prove ring_buffer_ext refinement end-to-end (zero sorry)
status: To Do
assignee: []
created_date: '2026-04-11 06:29'
labels:
  - milestone
  - verification
  - depth
dependencies:
  - TASK-0207
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The ring_buffer_ext_refines_queue_spec theorem currently has sorry (blocked on validHoare proofs). After sorry elimination (task-0207), verify this theorem compiles with zero sorry. This is THE deliverable: a complete refinement proof from abstract FIFO queue spec to C implementation, checked by the Lean kernel. Equivalent to seL4's L4.verified proof for a single subsystem.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 ring_buffer_ext_refines_queue_spec proven with zero sorry
- [ ] #2 #print axioms shows only propext/Quot.sound/Classical.choice
- [ ] #3 Refinement covers all 40 operations
- [ ] #4 Documented as worked example in user guide
<!-- AC:END -->
