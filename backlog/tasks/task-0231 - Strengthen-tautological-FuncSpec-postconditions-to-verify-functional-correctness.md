---
id: TASK-0231
title: >-
  Strengthen tautological FuncSpec postconditions to verify functional
  correctness
status: In Progress
assignee:
  - '@claude'
created_date: '2026-04-11 23:01'
updated_date: '2026-04-15 00:45'
labels:
  - sorry-elimination
  - ring-buffer
  - functional-correctness
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Several FuncSpecs (rb_count_nodes, rb_sum, rb_count_above, rb_count_at_or_below) have tautological postconditions (count=count). The validHoare proofs use validHoare_weaken_trivial_post to discharge them trivially. These proofs verify termination and absence of UB but NOT functional correctness. Strengthen each postcondition to state the actual result (e.g. ret_val = length of linked list, ret_val = sum of node values) and re-prove. Requires a recursive list abstraction (toList : HeapRawState -> Ptr -> List UInt32) to express the expected return value.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 rb_count_nodes_spec postcondition states ret_val = LinkedList.length
- [x] #2 rb_sum_spec postcondition states ret_val = sum of node values
- [ ] #3 rb_count_above_spec postcondition states ret_val = count of nodes above threshold
- [ ] #4 rb_count_at_or_below_spec postcondition states ret_val = count of nodes at or below threshold
- [ ] #5 All 4 validHoare proofs updated to prove strengthened postconditions
- [ ] #6 validHoare_weaken_trivial_post removed or deprecated
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Define LinkedListData (Type-level) in RBExtSpecs.lean for structural recursion
2. Define lengthU32, sumU32, countAboveU32, countAtOrBelowU32 on LinkedListData
3. Strengthen 4 specs: postcondition uses LinkedListData methods
4. Prove rb_count_nodes_validHoare with loop invariant carrying LinkedListData witness
5. Prove rb_sum_validHoare similarly
6. Prove rb_count_above_validHoare (has conditional in loop body)
7. Prove rb_count_at_or_below_validHoare similarly
8. Build and verify
<!-- SECTION:PLAN:END -->
