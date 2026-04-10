---
id: TASK-0136
title: Complete validHoare proofs for all 40 ring_buffer_ext functions
status: In Progress
assignee:
  - '@claude'
created_date: '2026-04-10 18:45'
updated_date: '2026-04-10 19:26'
labels:
  - phase-l
  - verification
  - critical
dependencies:
  - TASK-0135
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The biggest gap between us and seL4. We have FuncSpecs for 15/40 functions but validHoare PROOFS for only a handful. seL4 proved EVERY function. For each of the 40 functions: (1) write FuncSpec if not done, (2) prove validHoare using the [local irreducible] + projection simp pattern, (3) use Claude proof engine for bulk work. Target: 40/40 proven. This is the grinding work that makes verification real.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 FuncSpec defined for all 40 functions
- [ ] #2 validHoare proven for all 40 functions
- [ ] #3 No sorry in any proof
- [ ] #4 Automation rate measured: X/40 fully automatic, Y/40 needed hints, Z/40 manual
- [ ] #5 Total proof LOC measured
- [ ] #6 Average proof time per function measured
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
- 40/40 FuncSpecs defined (18 existing + 22 new in RBExtFuncSpecs.lean)
- 25/40 validHoare proofs use sorry (loops, multi-heap, calls)
- 0/40 fully proven yet (existing SwapProof pattern not yet applied to ring buffer)
<!-- SECTION:NOTES:END -->
