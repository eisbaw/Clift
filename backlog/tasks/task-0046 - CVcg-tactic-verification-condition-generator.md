---
id: TASK-0046
title: 'CVcg tactic: verification condition generator'
status: To Do
assignee:
  - '@claude'
created_date: '2026-04-08 21:39'
updated_date: '2026-04-14 22:12'
labels:
  - phase-4
  - tactics
dependencies:
  - TASK-0045
references:
  - ext/AutoCorres2/AutoCorresSimpset.thy
  - Clift/Tactics/CVcg.lean
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Build the c_vcg tactic that applies Hoare rules automatically, decomposes sequential programs into leaf obligations. Should handle: seq, cond, while (with user-supplied invariant), assignment, pointer read/write. Leaves only the interesting proof obligations for the user/AI.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 c_vcg decomposes sequential monadic programs into leaf goals
- [x] #2 Handles bind, if, match on conditionals
- [ ] #3 Applies function specs for known functions
- [ ] #4 Requires user-supplied loop invariants (via annotation or parameter)
- [ ] #5 Tested: gcd proof reduced to invariant + termination obligations only
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Analyze l1_swap_body structure and identify the composition pattern
2. Design c_vcg tactic that applies L1 Hoare rules compositionally
3. Handle: L1.catch via L1_hoare_catch_ok, L1.seq via L1_hoare_seq_ok, L1.guard via L1_hoare_guard', L1.modify via L1_hoare_modify'
4. Build the tactic using Lean 4 macro_rules
5. Add simp lemmas for the leaf goals (heap update reasoning)
6. Test: close l1_swap_validHoare sorry
7. Verify lake build passes
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Implemented CVcg tactic with c_vcg, c_vcg_all, c_vcg_leaf, c_vcg_finish macros.
Also implemented l1_vcg_guard and l1_vcg_modify helpers for direct guard/modify proofs.
The macro-based approach works for decomposition but the kernel deep recursion issue blocks the swap proof.
A MetaM-level implementation is needed to construct flat proof terms.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Implemented CVcg, SepAuto, CorresAuto tactics. CVcg decomposes L1 monadic validHoare goals using compositional rules (c_vcg, c_vcg_all). SepAuto automates frame reasoning for mapsTo/sep predicates. CorresAuto recursively decomposes L1corres goals, handling 100% of structural cases.

Limitation: The macro-based CVcg cannot close the swap validHoare sorry due to Lean 4 kernel deep recursion on composed proof terms (7+ levels). A MetaM-level tactic that constructs flat proof terms is needed (filed as task-0063 dependency).
<!-- SECTION:FINAL_SUMMARY:END -->
