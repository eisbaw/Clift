---
id: TASK-0089
title: 'Phase B milestone: verify 10-function C file with inter-procedural calls'
status: To Do
assignee: []
created_date: '2026-04-10 05:17'
labels:
  - phase-b
  - milestone
  - test
dependencies:
  - TASK-0087
  - TASK-0088
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
End-to-end test: write or find a real 10-function C file (~200 LOC) where functions call each other. Run through full pipeline: CImporter -> clift -> function specs -> VCG -> proofs. Measure: automation %, proof-to-code ratio, time. This validates that Clift can handle real multi-function programs.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 10-function C file processed by CImporter
- [ ] #2 'clift' lifts all 10 functions automatically
- [ ] #3 Function specs written for all 10 functions
- [ ] #4 At least 5 functions fully verified (VCG + manual invariants)
- [ ] #5 Proof-to-code ratio measured
- [ ] #6 No sorry in verified functions
<!-- AC:END -->
