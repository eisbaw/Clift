---
id: TASK-0093
title: 'Linked data structure verification: linked list traversal'
status: To Do
assignee: []
created_date: '2026-04-10 05:18'
labels:
  - phase-c
  - test
  - seplogic
  - milestone
dependencies:
  - TASK-0092
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Verify a C function that traverses a linked list (list_length or list_sum). This requires: an abstract list predicate (isList : Ptr Node -> List Nat -> HeapPred) connecting the C heap representation to a Lean List, a loop invariant relating the traversal position to a suffix of the abstract list, and frame reasoning showing the traversal doesn't modify the list. This is the canonical test for heap verification tools.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 isList predicate defined: recursive mapsTo chain
- [ ] #2 list_length verified: returns List.length of the abstract list
- [ ] #3 Loop invariant: isList cursor suffix * isList_prefix prefix
- [ ] #4 Frame: list is not modified during traversal
- [ ] #5 Proof uses sep_auto for frame reasoning
- [ ] #6 No sorry
<!-- AC:END -->
