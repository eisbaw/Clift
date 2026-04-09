---
id: TASK-0063
title: Eliminate sorry in l1_swap_validHoare via c_vcg tactic or flat proof terms
status: In Progress
assignee:
  - '@claude'
created_date: '2026-04-09 16:52'
updated_date: '2026-04-09 19:15'
labels:
  - phase-4
  - sorry
  - technical-debt
dependencies:
  - TASK-0046
references:
  - Examples/SwapProof.lean
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
SwapProof.lean:117 has a sorry in l1_swap_validHoare. The proof is mathematically trivial (deterministic computation trace) but hits two Lean 4 kernel limitations: (1) deep recursion limit when composing 7+ L1 Hoare rules, (2) have/let binding mismatch in structure update desugaring. Fix after Phase 4 c_vcg tactic is available, or by restructuring l1_swap_body to use flat CState.mk constructors instead of { s with ... }.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 l1_swap_validHoare proven with no sorry
- [ ] #2 swap_correct depends only on propext/Quot.sound (no sorryAx)
- [ ] #3 lake build produces no sorry warnings
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Attempted multiple proof strategies for l1_swap_validHoare:
1. Compositional Hoare rules (L1_hoare_seq + guard + modify) - fails: kernel deep recursion from nested rule composition
2. Direct set membership chaining (L1_guard_modify_result + L1_seq_singleton_ok) - fails: state naming hits have/let desugaring mismatch
3. Rewriting body with explicit constructors - fails: rfl check hits deep recursion
4. Combined vcg helpers (l1_vcg_guard, l1_vcg_modify) - gets furthest but still hits kernel deep recursion at ~7 nested levels

Root cause: Lean 4 kernel deep recursion limit on proof terms composed from 7+ nested Hoare rule applications. The proof is mathematically trivial but the kernel cannot handle the term depth.

Required solution: A MetaM-level VCG tactic that constructs FLAT proof terms by unfolding validHoare and directly building set membership witnesses, bypassing the compositional rule composition entirely.
<!-- SECTION:NOTES:END -->
