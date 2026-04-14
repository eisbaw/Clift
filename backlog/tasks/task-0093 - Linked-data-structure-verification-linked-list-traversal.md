---
id: TASK-0093
title: 'Linked data structure verification: linked list traversal'
status: To Do
assignee:
  - '@claude'
created_date: '2026-04-10 05:18'
updated_date: '2026-04-14 22:12'
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
- [x] #1 isList predicate defined: recursive mapsTo chain
- [ ] #2 list_length verified: returns List.length of the abstract list
- [x] #3 Loop invariant: isList cursor suffix * isList_prefix prefix
- [x] #4 Frame: list is not modified during traversal
- [ ] #5 Proof uses sep_auto for frame reasoning
- [x] #6 No sorry
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Define isList: Ptr C_node -> List Nat -> HeapPred (recursive chain of mapsTo)
2. Define L1 monadic version of list_length_body
3. Prove L1corres for list_length
4. Define loop invariant: isList cursor suffix, count = length of prefix
5. Prove list_length returns List.length using wp + invariant
6. Frame: list is not modified during traversal
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
- isList defined as inductive: nil (null -> []) and cons (valid ptr -> v::vs)
- Loop invariant: listLengthInv tracks suffix, count = length of prefix
- Exit theorem: head=null implies count=length (sorry-free)
- Step theorem: listLengthInv_advance maintains invariant (sorry-free, uses native_decide for UInt32)
- Frame: list_length_read_only proves traversal preserves any mapsTo
- AC#2 (full validHoare for l1_list_length_body): requires mechanical L1 combinator trace, deferred
- AC#5 (sep_auto usage): the proofs use manual sep logic, sep_auto applicable to individual goals
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Linked list traversal verification infrastructure for list_length.

Key additions:
- isList inductive predicate: recursive mapsTo chain for C linked lists
- isList properties: null_iff, nonnull, null (sorry-free)
- Loop invariant: listLengthInv with suffix tracking + UInt32 overflow guard
- Invariant init/exit/advance theorems (all sorry-free)
- Frame theorem: read-only traversal preserves disjoint heap assertions
- UInt32 addition overflow handled via xs.length < 2^32 precondition

Limitations:
- Full validHoare proof for l1_list_length_body requires mechanical L1 combinator trace (same technique as SwapProof.lean)
- Proof-to-code ratio: ~100:10 = 10:1 (higher than 5:1 target, but includes reusable infrastructure)

Files: Examples/ListLengthProof.lean
<!-- SECTION:FINAL_SUMMARY:END -->
