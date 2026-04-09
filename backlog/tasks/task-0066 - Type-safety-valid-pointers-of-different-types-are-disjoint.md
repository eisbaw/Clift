---
id: TASK-0066
title: 'Type-safety: valid pointers of different types are disjoint'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-09 17:13'
updated_date: '2026-04-09 20:10'
labels:
  - phase-3c
  - soundness
dependencies:
  - TASK-0064
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
In Tuch's POPL 2007 model, the heap typing ensures that two valid pointers of different types have disjoint footprints. Our model does not enforce this. We need a theorem: if heapPtrValid h p and heapPtrValid h q and CType.typeTag p \!= CType.typeTag q, then ptrDisjoint p q. This requires strengthening the htd to track full footprints (see task for footprint check).
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Theorem: different-type valid pointers are disjoint
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Proved heapPtrValid_different_type_disjoint: if two pointers have different type tags and are both valid, their footprints are disjoint. Proof by contradiction: if the footprints overlap, a shared byte would have two different type tags via the strengthened htd (task-0064), which is impossible since htd assigns exactly one tag per byte. This is the Lean 4 analog of Tuch POPL 2007 Lemma 3.2.
<!-- SECTION:FINAL_SUMMARY:END -->
