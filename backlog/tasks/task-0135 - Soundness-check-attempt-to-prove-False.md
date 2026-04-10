---
id: TASK-0135
title: 'Soundness check: attempt to prove False'
status: To Do
assignee: []
created_date: '2026-04-10 18:45'
labels:
  - phase-l
  - soundness
  - critical
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The cheapest, highest-value test. If we can prove False without sorry, the entire system is unsound and every proof is meaningless. Try: (1) derive False from corres + L1corres assumptions, (2) derive False from the memory model (heapPtrValid + hVal + heapUpdate), (3) derive False from the Exec semantics, (4) derive False from NondetM + Hoare triples. If any succeed: we have a critical bug. If all fail: confidence boost. seL4 had multiple independent kernel checkers specifically to catch this class of error.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Attempted: prove False from corres definitions alone
- [ ] #2 Attempted: prove False from memory model
- [ ] #3 Attempted: prove False from Exec semantics
- [ ] #4 Attempted: prove False from NondetM/Hoare
- [ ] #5 Attempted: prove False from L1corres bridge
- [ ] #6 Result documented: all attempts failed (good) or bug found (critical)
- [ ] #7 If bug found: filed as blocking task with fix
<!-- AC:END -->
