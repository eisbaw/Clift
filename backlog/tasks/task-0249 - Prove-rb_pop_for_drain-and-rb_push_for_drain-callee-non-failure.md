---
id: TASK-0249
title: Prove rb_pop_for_drain and rb_push_for_drain callee non-failure
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
2 sorry in RBExtProofRbDrainTo.lean (lines 148, 178): callee non-failure for rb_pop and rb_push inside drain_to.

CORRECTION: L1.catch body L1.skip does NOT suppress failure — catch propagates body.failed. So full guard chain reasoning is needed.

rb_pop_for_drain (line 148): head≠null case. Need to chase ~10 heapPtrValid guards through the rb_pop body. Pattern: same as RBExtProofRbPop.lean parts 1+2 (~130 lines). Null case already proven via L1_catch_seq_error_first_nf.

rb_push_for_drain (line 178): not-full case. Need ~100 lines of guard chain reasoning. Blocker: rb_push_spec requires ptrDisjoint(node, dst.tail) which drain_to precondition lacks. Fix: define rb_push_nf_spec (non-failure only, no ptrDisjoint) or add ptrDisjoint to drain_to's loop invariant.

Approach: copy the guard chain proofs from RBExtProofRbPop.lean and adapt inline, or import rb_pop_validHoare and derive non-failure from it.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 rb_pop_for_drain proven (0 sorry)
- [ ] #2 rb_push_for_drain proven (0 sorry)
<!-- AC:END -->
