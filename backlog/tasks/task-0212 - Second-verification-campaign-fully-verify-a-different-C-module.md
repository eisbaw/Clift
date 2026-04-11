---
id: TASK-0212
title: 'Second verification campaign: fully verify a different C module'
status: To Do
assignee: []
created_date: '2026-04-11 06:29'
labels:
  - verification
  - depth
  - milestone
dependencies:
  - TASK-0211
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
One verified module could be a fluke. Verify a second module end-to-end with zero sorry: pick one of RTOS queue, SHA-256, UART driver, or packet parser. Full pipeline: import, lift, abstract spec, invariants, per-function FuncSpecs, validHoare proofs, refinement theorem. Measure effort and compare with ring buffer. This validates the tool is general, not module-specific.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Second module selected (different domain from ring buffer)
- [ ] #2 All functions have FuncSpecs with full functional correctness postconditions
- [ ] #3 All validHoare proofs complete (zero sorry)
- [ ] #4 Refinement theorem proven
- [ ] #5 Effort measured and compared with ring buffer
<!-- AC:END -->
