---
id: TASK-0005
title: 'Prove Hoare rules: cond, while-invariant, frame'
status: To Do
assignee: []
created_date: '2026-04-08 21:33'
labels:
  - phase-0
  - monadlib
dependencies:
  - TASK-0004
references:
  - ext/AutoCorres2/lib/Monad_WP/NonDetMonadVCG.thy
  - ext/simpl-schirmer.pdf
  - Clift/MonadLib/HoareRules.lean
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Prove Hoare rules for conditionals, while loops (with invariant), and the frame rule. The while rule is critical — it requires an invariant and a variant (for total correctness). The frame rule enables modular reasoning. Study Simpl's HoarePartialDef.thy.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 hoare_cond: conditional rule proven for both branches
- [ ] #2 hoare_while: while-invariant rule proven (partial correctness)
- [ ] #3 hoare_while_total: while-invariant + variant rule proven (total correctness)
- [ ] #4 hoare_frame: frame rule proven
- [ ] #5 All proofs use no sorry
<!-- AC:END -->
