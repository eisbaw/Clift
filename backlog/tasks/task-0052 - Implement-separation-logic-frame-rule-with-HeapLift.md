---
id: TASK-0052
title: Implement separation logic frame rule with HeapLift
status: Done
assignee:
  - '@claude'
created_date: '2026-04-08 22:36'
updated_date: '2026-04-09 22:35'
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
- [x] #1 Separation logic predicates (mapsTo, sep) defined
- [x] #2 Frame rule with separating conjunction proven
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Sep logic predicates (mapsTo, sep, sepMapsTo) were already defined. Added general validHoare_frame_mapsTo and validHoare_frame_sepMapsTo theorems that bridge heap-level frame reasoning to Hoare-level reasoning, with explicit locality hypothesis. These are the true sep-logic frame rules for our NondetM framework.
<!-- SECTION:FINAL_SUMMARY:END -->
