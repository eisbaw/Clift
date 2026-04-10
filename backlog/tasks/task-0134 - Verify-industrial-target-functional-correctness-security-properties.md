---
id: TASK-0134
title: 'Verify industrial target: functional correctness + security properties'
status: To Do
assignee: []
created_date: '2026-04-10 15:31'
labels:
  - phase-k
  - industrial
  - milestone
dependencies:
  - TASK-0133
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The deliverable that proves Clift is industrially useful. Verify the selected target: (1) import all C files, (2) lift all functions, (3) write abstract spec, (4) define global invariants, (5) prove per-function correctness, (6) prove security properties. Use Claude proof engine for bulk proof work. Measure total effort. Compare with seL4's effort for equivalent complexity.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 All C files imported and lifted
- [ ] #2 Abstract spec written and reviewed
- [ ] #3 Global invariants defined
- [ ] #4 At least 50% of functions fully verified
- [ ] #5 At least 1 security property proven (integrity or confidentiality)
- [ ] #6 Total effort measured in person-weeks
- [ ] #7 Comparison with seL4 effort documented
- [ ] #8 Paper-worthy result: we verified X with Y effort using Clift
<!-- AC:END -->
