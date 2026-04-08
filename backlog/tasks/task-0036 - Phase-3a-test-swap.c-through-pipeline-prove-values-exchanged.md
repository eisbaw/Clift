---
id: TASK-0036
title: 'Phase 3a test: swap.c through pipeline, prove values exchanged'
status: To Do
assignee: []
created_date: '2026-04-08 21:38'
labels:
  - phase-3a
  - test
  - milestone
dependencies:
  - TASK-0035
  - TASK-0030
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Run swap.c through the full pipeline (CImporter -> L1 -> L2 -> L3 -> L5). Prove that after swap(&a, &b), *a and *b are exchanged. This is the first pointer verification test.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 swap.c imports, lifts through L1-L2-L3-L5
- [ ] #2 theorem swap_correct proven: *a and *b exchanged
- [ ] #3 Proof handles pointer validity preconditions
- [ ] #4 No sorry in proof
<!-- AC:END -->
