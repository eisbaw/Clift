---
id: TASK-0211
title: Prove ring_buffer_ext refinement end-to-end (zero sorry)
status: To Do
assignee: []
created_date: '2026-04-11 06:29'
updated_date: '2026-04-11 08:45'
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

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Blocked on task 0189 (validHoare proofs). ring_buffer_ext_refines_queue_spec requires all 40 validHoare proofs. Currently only 4 of 40 are proven (rb_capacity, rb_size, rb_remaining, rb_stats_total_ops). The refinement theorem has 3 sorry that are all transitively blocked on the 25 remaining validHoare sorry.
<!-- SECTION:FINAL_SUMMARY:END -->
