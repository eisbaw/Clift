---
id: TASK-0052
title: Implement separation logic frame rule with HeapLift
status: To Do
assignee: []
created_date: '2026-04-08 22:36'
labels:
  - phase-3
  - monadlib
  - sep-logic
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The current hoare_frame in HoareRules.lean is just conjunction of two validHoare proofs -- it requires the user to independently prove R is preserved. The true separation logic frame rule (with separating conjunction and locality) must be added in Phase 3 when HeapLift provides typed split heaps.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Separation logic predicates (mapsTo, sep) defined
- [ ] #2 Frame rule with separating conjunction proven
<!-- AC:END -->
