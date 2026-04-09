---
id: TASK-0079
title: Fix GcdTypeStrengthen and GcdPhase2 proofs after division guard addition
status: To Do
assignee: []
created_date: '2026-04-09 20:38'
labels:
  - cimporter
  - proof-fix
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The addition of division-by-zero guards (task-0059) changed the L1 monad structure of gcd_while_body. Two proofs now use sorry: gcd_while_body_result in GcdTypeStrengthen and gcd_body_only_ok in GcdPhase2. The fix is mechanical -- after simp [hb], the goal is a membership in a singleton set with struct equality. Need to extract the equalities correctly.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 GcdTypeStrengthen.gcd_while_body_result proof closes without sorry
- [ ] #2 GcdPhase2.gcd_body_only_ok proof closes without sorry
<!-- AC:END -->
