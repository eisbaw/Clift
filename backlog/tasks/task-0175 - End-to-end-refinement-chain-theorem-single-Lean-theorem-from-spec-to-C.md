---
id: TASK-0175
title: 'End-to-end refinement chain theorem: single Lean theorem from spec to C'
status: In Progress
assignee:
  - '@claude'
created_date: '2026-04-10 18:53'
updated_date: '2026-04-10 19:26'
labels:
  - phase-l
  - seL4-parity
  - milestone
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The Clift pipeline has 5 stages (L1-L5), each with a corres lemma. seL4 composes these into explicit end-to-end theorems: 'property P of abstract spec implies P of C implementation'. TASK-0138 covers 'composed system-level correctness' but is vague. Need an explicit task: (1) Compose L1corres + L2corres + L3corres + L4corres + L5corres via corres_trans into ONE theorem, (2) State it cleanly: 'if AbstractSpec satisfies property P, then the C code (CSimpl) satisfies the corresponding concrete property', (3) Demonstrate with ring_buffer_ext: one function, full chain from Nat-level spec to CSimpl, as a SINGLE theorem statement. This is what a formal methods reviewer will look for first.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Single composed corres theorem spanning all 5 stages
- [x] #2 Clean statement: abstract property => C property
- [x] #3 Demonstrated on at least one ring_buffer_ext function
- [ ] #4 Proof term checked by Lean kernel without sorry
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
- SystemRefinement structure defined
- extQueueImpl maps all 40 ops to L1 bodies
- ring_buffer_ext_refines_queue_spec stated (sorry: blocked on task 0136)
- fifo_holds_at_c_level demonstrated (sorry: blocked on refinement)
- 3 sorry total, all transitively blocked on validHoare proofs
<!-- SECTION:NOTES:END -->
