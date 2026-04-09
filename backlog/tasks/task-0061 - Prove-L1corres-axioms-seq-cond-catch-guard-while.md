---
id: TASK-0061
title: 'Prove L1corres axioms: seq, cond, catch, guard, while'
status: Done
assignee:
  - '@mped'
created_date: '2026-04-08 23:54'
updated_date: '2026-04-09 00:07'
labels:
  - phase-1
  - lifting
  - proofs
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The L1corres lemmas for seq, cond, catch, guard, while are currently axioms in Clift/Lifting/SimplConv.lean. These need to be proved as theorems. The proofs require careful set membership reasoning about NondetM results/failure. Each proof follows the same pattern: extract non-failure from the composed monad, use the sub-lemmas to get membership in sub-results, then show membership in the composed results. The while proof requires induction on the Exec derivation with equation generalization.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 L1corres_seq proved (no axiom)
- [x] #2 L1corres_cond proved
- [x] #3 L1corres_catch proved
- [x] #4 L1corres_guard proved
- [x] #5 L1corres_while proved
- [x] #6 No axioms remain in SimplConv.lean
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
All 5 L1corres axioms proved as theorems in Clift/Lifting/SimplConv.lean:

- L1corres_seq: set membership reasoning on L1.seq result/failure sets
- L1corres_cond: case split on boolean condition, delegate to sub-corres
- L1corres_catch: set membership on L1.catch, body/handler failure propagation
- L1corres_guard: extract predicate from non-failure, reduce guard+seq to body
- L1corres_while: generalized induction on Exec with command-equation hypothesis, construct L1.WhileResult from Exec derivation

Helper lemmas for failure propagation (L1_seq_not_failed_left/right, L1_catch_not_failed_body/handler, L1_while_body_not_failed, L1_while_step_not_failed).

No axioms or sorry remain in the codebase. lake build succeeds, all e2e tests pass.
<!-- SECTION:FINAL_SUMMARY:END -->
