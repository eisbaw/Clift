---
id: TASK-0041
title: 'HeapLift (L4): define simpleLift and typed heap access'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-08 21:38'
updated_date: '2026-04-09 18:03'
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
- [x] #1 simpleLift : HeapRawState -> Ptr α -> Option α defined
- [x] #2 Typed heap state with per-type heap maps defined
- [x] #3 Abstraction relation between raw heap and typed heaps defined
- [x] #4 Lift/unlift roundtrip lemma proven
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
simpleLift, simpleUpdate defined in SimpleLift.lean. TypedHeap abstraction in SplitHeap.lean. All lemmas proved: simpleLift_some, simpleLift_val, simpleLift_none, simpleLift_update_same, simpleLift_update_disjoint. typedHeapOf_agrees roundtrip proved. No sorry.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Implemented simpleLift (HeapRawState -> Ptr a -> Option a) and simpleUpdate following AutoCorres2 TypHeapSimple.thy. Proved simpleLift_some, simpleLift_val, simpleLift_update_same, simpleLift_update_disjoint. SplitHeap.lean provides TypedHeap abstraction with typedHeapOf and agreement relation. All proofs complete, zero sorry.
<!-- SECTION:FINAL_SUMMARY:END -->
