---
id: TASK-0239
title: Close rb_drain_to sorry (loop + dual dynCom)
status: To Do
assignee: []
created_date: '2026-04-13 09:53'
labels:
  - sorry-elimination
  - inter-procedural
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
1 sorry in RBExtProofRbDrainTo.lean. The function loops calling rb_pop then rb_push via dynCom per iteration.

BLOCKERS (from agent analysis):
1. Frame rule: after opaque dynCom call, need heapPtrValid preserved for pointers NOT in callee spec. Solution: prove heapPtrValid_preserved_through_L1 theorem.
2. ptrDisjoint self-aliasing: rb_push_spec requires ptrDisjoint(node, dst.tail). After first push, dst.tail=node. Fix: define rb_push_spec_weak without ptrDisjoint (for non-failure only).
3. LinkedListValid maintenance through callee heap modifications: need WellFormedList in precondition.

L1_hoare_dynCom_call infrastructure exists and works (proven for check_integrity, push_if_not_full, pop_if_not_empty). The challenge is composing TWO dynCom calls per loop iteration.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 rb_drain_to_validHoare proven with 0 sorry
<!-- AC:END -->
