---
id: TASK-0028
title: 'TypeStrengthen (L3): MetaM to analyze and narrow monad'
status: To Do
assignee: []
created_date: '2026-04-08 21:36'
labels:
  - phase-2
  - lifting
  - metam
dependencies:
  - TASK-0027
references:
  - ext/AutoCorres2/type_strengthen.ML
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Write MetaM that analyzes each L2 function: can it fail? Does it modify state? Select the tightest monad and generate L3corres proof. Pattern-match L2 term structure against ts_rules. Study type_strengthen.ML for the Isabelle implementation.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Functions that cannot fail and do not use state are typed as pure
- [ ] #2 Functions that can fail are typed as option or nondet
- [ ] #3 L3corres proof generated for each function
- [ ] #4 gcd.c: gcd becomes pure (Nat -> Nat -> Nat after WordAbstract)
- [ ] #5 All proofs kernel-checked, no sorry
<!-- AC:END -->
