---
id: TASK-0042
title: 'HeapLift (L4): MetaM for heap abstraction + corres proof'
status: To Do
assignee: []
created_date: '2026-04-08 21:38'
labels:
  - phase-3c
  - lifting
  - metam
dependencies:
  - TASK-0041
references:
  - ext/AutoCorres2/heap_lift.ML
  - ext/AutoCorres2/HeapLift.thy
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Write MetaM that transforms L3 functions by replacing raw heap operations (hVal, heapUpdate) with typed heap operations (simpleLift, typed write). Generate HLcorres proof relating raw and typed heap states. Study heap_lift.ML.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 MetaM rewrites hVal calls to simpleLift calls
- [ ] #2 MetaM rewrites heapUpdate calls to typed heap writes
- [ ] #3 HLcorres proof generated for each function
- [ ] #4 swap.c lifts through HeapLift correctly
<!-- AC:END -->
