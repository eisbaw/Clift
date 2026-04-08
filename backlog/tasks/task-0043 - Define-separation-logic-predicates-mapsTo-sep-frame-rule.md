---
id: TASK-0043
title: 'Define separation logic predicates: mapsTo, sep, frame rule'
status: To Do
assignee: []
created_date: '2026-04-08 21:38'
labels:
  - phase-3d
  - seplogic
dependencies:
  - TASK-0041
references:
  - ext/AutoCorres2/Split_Heap.thy
  - ext/tuch-types-bytes-seplogic-popl2007.pdf
  - Clift/Lifting/HeapLift/SepLogic.lean
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Define basic separation logic predicates over the typed split heap: mapsTo (pointer points to value), sep (separating conjunction — disjoint heap regions), emp (empty heap). Prove the frame rule: {P} c {Q} implies {P * R} c {Q * R}. These are needed for pointer reasoning. No automation yet — manual application.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 mapsTo p v : Ptr α -> α -> HeapPred defined
- [ ] #2 sep P Q : separating conjunction defined
- [ ] #3 emp : empty heap predicate defined
- [ ] #4 Frame rule theorem proven
- [ ] #5 Basic sep lemmas: sep_comm, sep_assoc proven
<!-- AC:END -->
