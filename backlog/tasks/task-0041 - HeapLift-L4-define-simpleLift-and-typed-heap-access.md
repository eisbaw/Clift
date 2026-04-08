---
id: TASK-0041
title: 'HeapLift (L4): define simpleLift and typed heap access'
status: To Do
assignee: []
created_date: '2026-04-08 21:38'
labels:
  - phase-3c
  - lifting
dependencies:
  - TASK-0040
references:
  - ext/AutoCorres2/TypHeapSimple.thy
  - ext/AutoCorres2/Split_Heap.thy
  - Clift/Lifting/HeapLift/SimpleLift.lean
  - Clift/Lifting/HeapLift/SplitHeap.lean
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Implement simpleLift following AutoCorres2's TypHeapSimple.thy. simpleLift reads a typed value from the raw heap if the pointer is valid. Define typed heap state (per-type heaps). Restriction: no nested struct field pointers — access structs as whole values.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 simpleLift : HeapRawState -> Ptr α -> Option α defined
- [ ] #2 Typed heap state with per-type heap maps defined
- [ ] #3 Abstraction relation between raw heap and typed heaps defined
- [ ] #4 Lift/unlift roundtrip lemma proven
<!-- AC:END -->
