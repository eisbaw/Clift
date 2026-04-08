---
id: TASK-0009
title: Prove corres transitivity and composition
status: Done
assignee:
  - '@mped'
created_date: '2026-04-08 21:34'
updated_date: '2026-04-08 22:48'
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
- [x] #1 corres_trans: transitivity theorem proven
- [x] #2 corres_guard_imp: guard weakening proven
- [x] #3 corres_split: sequential composition splitting proven
- [x] #4 All proofs kernel-checked, no sorry
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Proved all three key corres rules:

1. corres_trans: transitivity with composed state/return relations. Requires intermediate nf'=true.
2. corres_guard_imp: guard weakening (direct analogue of Hoare consequence rule).
3. corres_split: sequential composition with h_abs_nf for abstract no-fail. Also corres_split_nf_false for the common partial correctness case.
4. corres_fail_fail: trivial corres for fail on both sides.

Subtlety in corres_split: abstract no-fail for bind requires proving ALL abstract continuations dont fail, not just those matching concrete results. This is a fundamental property of backward simulation -- the abstract may have more behaviors than the concrete. Handled by explicit h_abs_nf argument.

All proofs kernel-checked, zero sorry.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Proved corres transitivity and composition rules in Clift/MonadLib/CorresRules.lean.

Theorems proven:
- corres_trans: chains refinement steps, composing state and return relations existentially
- corres_guard_imp: weakens guards (preconditions)
- corres_split: sequential composition via bind, with explicit abstract no-fail obligation
- corres_split_nf_false: simplified split for partial correctness (nf=false)
- corres_fail_fail: corres for fail on both sides

All proofs kernel-checked, zero sorry. Build passes clean.
<!-- SECTION:FINAL_SUMMARY:END -->
