---
id: TASK-0009
title: Prove corres transitivity and composition
status: To Do
assignee: []
created_date: '2026-04-08 21:34'
labels:
  - phase-0
  - monadlib
dependencies:
  - TASK-0008
references:
  - ext/AutoCorres2/CorresXF.thy
  - Clift/MonadLib/CorresRules.lean
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Prove that corres composes transitively — chains L1->L2->L3->L4->L5 into end-to-end refinement. Also prove corres_guard_imp (weakening guards) and corres_split (sequential composition). Study ext/AutoCorres2/CorresXF.thy.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 corres_trans: transitivity theorem proven
- [ ] #2 corres_guard_imp: guard weakening proven
- [ ] #3 corres_split: sequential composition splitting proven
- [ ] #4 All proofs kernel-checked, no sorry
<!-- AC:END -->
