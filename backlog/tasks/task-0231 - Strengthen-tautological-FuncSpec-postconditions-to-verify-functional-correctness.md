---
id: TASK-0231
title: >-
  Strengthen tautological FuncSpec postconditions to verify functional
  correctness
status: To Do
assignee: []
created_date: '2026-04-11 23:01'
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
- [ ] #1 rb_count_nodes_spec postcondition states ret_val = LinkedList.length
- [ ] #2 rb_sum_spec postcondition states ret_val = sum of node values
- [ ] #3 rb_count_above_spec postcondition states ret_val = count of nodes above threshold
- [ ] #4 rb_count_at_or_below_spec postcondition states ret_val = count of nodes at or below threshold
- [ ] #5 All 4 validHoare proofs updated to prove strengthened postconditions
- [ ] #6 validHoare_weaken_trivial_post removed or deprecated
<!-- AC:END -->
