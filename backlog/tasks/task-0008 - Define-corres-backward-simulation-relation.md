---
id: TASK-0008
title: Define corres (backward simulation) relation
status: Done
assignee:
  - '@mped'
created_date: '2026-04-08 21:34'
updated_date: '2026-04-08 22:44'
labels:
  - phase-0
  - monadlib
dependencies:
  - TASK-0001
references:
  - ext/AutoCorres2/CorresXF.thy
  - Clift/MonadLib/Corres.lean
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Define the correspondence/refinement relation following seL4's corres_underlying. Must use backward simulation: for every concrete result, abstract has a matching one. Include state relation, no-fail flags, return value relation, and guard preconditions. This is the most critical definition — get it wrong and everything downstream is unsound.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 corres definition matches plan.md Decision 1 exactly
- [x] #2 Backward simulation direction verified: concrete results imply abstract results
- [x] #3 State relation, no-fail flags, return relation, guards all present
- [x] #4 Sanity test: corres Id true true Eq True True (pure x) (pure x) proven trivially
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
corres definition matches plan.md Decision 1 exactly.
Backward simulation: concrete results imply abstract results.
Sanity test pure_pure_eq proves corres for identical pure computations.
Also proved weakening lemmas (weaken_nf, weaken_nf').
No sorry in any proof.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Defined corres backward simulation relation in Clift/MonadLib/Corres.lean.

The definition takes: state relation srel, no-fail flags nf/nf', return relation rrel, guards G/G', abstract and concrete NondetM computations.

Proved:
- pure_pure: corres holds for pure computations with related values
- pure_pure_eq: sanity test with identity relations
- weaken_nf/weaken_nf': no-fail flag weakening

All proofs kernel-checked, zero sorry.
<!-- SECTION:FINAL_SUMMARY:END -->
