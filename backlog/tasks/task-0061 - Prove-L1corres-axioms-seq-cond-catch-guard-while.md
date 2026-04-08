---
id: TASK-0061
title: 'Prove L1corres axioms: seq, cond, catch, guard, while'
status: To Do
assignee: []
created_date: '2026-04-08 23:54'
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
- [ ] #1 L1corres_seq proved (no axiom)
- [ ] #2 L1corres_cond proved
- [ ] #3 L1corres_catch proved
- [ ] #4 L1corres_guard proved
- [ ] #5 L1corres_while proved
- [ ] #6 No axioms remain in SimplConv.lean
<!-- AC:END -->
