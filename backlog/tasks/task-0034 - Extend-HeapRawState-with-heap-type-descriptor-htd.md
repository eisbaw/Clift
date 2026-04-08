---
id: TASK-0034
title: Extend HeapRawState with heap type descriptor (htd)
status: To Do
assignee: []
created_date: '2026-04-08 21:37'
labels:
  - phase-3a
  - csemantics
dependencies:
  - TASK-0032
references:
  - ext/AutoCorres2/TypHeapSimple.thy
  - Clift/CSemantics/State.lean
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Extend HeapRawState with a proper heap type descriptor that tracks what type is stored at each address. Define heapPtrValid predicate. Define hVal (read typed value from raw bytes). Study ext/AutoCorres2/TypHeapSimple.thy for the simplified model.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 HeapRawState.htd field tracks type at each address
- [ ] #2 heapPtrValid p s defined: pointer p is valid in state s
- [ ] #3 hVal s p : read typed value from raw bytes at pointer address
- [ ] #4 heapUpdate s p v : write typed value to raw bytes
- [ ] #5 Basic lemma: hVal (heapUpdate s p v) p = v proven
<!-- AC:END -->
