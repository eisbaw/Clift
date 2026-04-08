---
id: TASK-0032
title: 'Phase 2 end-to-end: gcd lifts to Nat -> Nat -> Nat'
status: To Do
assignee: []
created_date: '2026-04-08 21:37'
labels:
  - phase-2
  - test
  - milestone
dependencies:
  - TASK-0030
  - TASK-0031
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Phase 2 exit criterion: gcd.c through full pipeline (CImporter -> L1 -> L2 -> L3 -> L5) produces a pure Nat -> Nat -> Nat function. User proves gcd_correct using omega and Nat reasoning only — no BitVec. Proof chains all the way to C.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 gcd lifts to pure type (not option, not nondet)
- [ ] #2 gcd return type is Nat (not BitVec 32)
- [ ] #3 gcd_correct proven using omega and Nat lemmas
- [ ] #4 Full corres chain: L1corres o L2corres o L3corres o WAcorres
- [ ] #5 just e2e passes
<!-- AC:END -->
