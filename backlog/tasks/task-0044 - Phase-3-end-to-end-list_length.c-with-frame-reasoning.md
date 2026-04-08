---
id: TASK-0044
title: 'Phase 3 end-to-end: list_length.c with frame reasoning'
status: To Do
assignee: []
created_date: '2026-04-08 21:38'
labels:
  - phase-3
  - test
  - milestone
dependencies:
  - TASK-0042
  - TASK-0043
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Phase 3 exit criterion: list_length.c through full pipeline, prove it returns the length of the abstract list. Also prove swap.c with frame reasoning: other memory is unchanged. These are the first real pointer verification results.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 list_length.c through full pipeline (all 5 stages)
- [ ] #2 theorem list_length_correct proven: returns List.length of abstract list
- [ ] #3 swap.c proven with frame: only *a and *b change, rest of heap unchanged
- [ ] #4 Proofs use separation logic predicates (mapsTo, sep)
- [ ] #5 just e2e passes with all Phase 3 tests
<!-- AC:END -->
