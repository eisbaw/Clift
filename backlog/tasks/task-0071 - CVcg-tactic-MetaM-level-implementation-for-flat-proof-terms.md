---
id: TASK-0071
title: 'CVcg tactic: MetaM-level implementation for flat proof terms'
status: To Do
assignee:
  - '@claude'
created_date: '2026-04-09 19:34'
updated_date: '2026-04-14 22:12'
labels:
  - phase-5
  - tactics
  - metam
dependencies:
  - TASK-0046
references:
  - ext/AutoCorres2/autocorres.ML
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The current CVcg tactic (macro-based) hits Lean 4 kernel deep recursion for programs with 7+ sequential steps. Need a MetaM-level VCG that constructs FLAT proof terms directly, bypassing the kernel depth issue. This is what AutoCorres2 does in Isabelle/ML. The MetaM VCG should decompose validHoare goals into leaf obligations without nesting proof terms deeper than ~3 levels. This would fix the sorry in SwapProof.lean.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 MetaM VCG constructs flat proof terms
- [ ] #2 l1_swap_validHoare proven (SwapProof.lean sorry eliminated)
- [ ] #3 Works on programs with 10+ sequential L1 steps
- [ ] #4 No sorry
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
The SwapProof.lean sorry was eliminated without MetaM VCG. The two-level projection lemma strategy (show+rfl with [local irreducible] for first-level, rw for second-level) avoids kernel deep recursion. The MetaM VCG is still useful for automating proofs of larger programs but is no longer a blocker for the swap proof.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
The sorry was fixed WITHOUT MetaM VCG. The irreducible+simp approach is sufficient.

The key insight: the kernel depth issue was caused by hVal/heapUpdate unfolding through byte-level arithmetic (UInt32 fromBytes/toBytes -> BitVec -> Nat div/mod). Marking these as [local irreducible] prevents the kernel from unfolding them, while simp lemmas handle the rewriting at the proof level.

A MetaM VCG would still be valuable for automation (avoiding manual step-by-step proofs), but it is not needed for soundness. Deferred to future work.
<!-- SECTION:FINAL_SUMMARY:END -->
