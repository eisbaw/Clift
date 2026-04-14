---
id: TASK-0250
title: 'Prove drain_to while loop body obligations (h_body_nf, h_body_inv, h_abrupt)'
status: To Do
assignee: []
created_date: '2026-04-14 07:02'
labels:
  - sorry-elimination
  - drain-to
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
3 sorry in RBExtProofRbDrainTo.lean (lines 239, 246, 254): while loop body obligations.

Depends on: rb_pop_for_drain + rb_push_for_drain being proven first.

h_body_nf (line 239): compose callee non-failure through two dynCom calls using L1_hoare_dynCom_call. Template: how h_body_nf was proven in HashTableProof.lean for ht_lookup.

h_body_inv (line 246): invariant preservation. After rb_pop advances src.head and rb_push modifies dst, need heapPtrValid preserved for src, dst, node pointers. Requires LinkedListValid or WellFormedList in the invariant to ensure next-pointer validity.

h_abrupt (line 254): error results satisfy postcondition. Frame argument — error states have heap derived from initial via heapUpdates, heapPtrValid preserved unconditionally.

Estimated: ~200 lines total for all 3. Requires mature WellFormedList infrastructure (available in RBExtSpecs.lean).
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 h_body_nf proven
- [ ] #2 h_body_inv proven
- [ ] #3 h_abrupt proven
- [ ] #4 rb_drain_to_validHoare fully sorry-free
<!-- AC:END -->
