---
id: TASK-0066
title: 'Type-safety: valid pointers of different types are disjoint'
status: To Do
assignee: []
created_date: '2026-04-09 17:13'
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
- [ ] #1 Theorem: different-type valid pointers are disjoint
<!-- AC:END -->
