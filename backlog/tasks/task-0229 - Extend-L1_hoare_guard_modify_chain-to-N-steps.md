---
id: TASK-0229
title: Extend L1_hoare_guard_modify_chain to N steps
status: Done
assignee:
  - '@claude'
created_date: '2026-04-11 15:07'
updated_date: '2026-04-12 04:02'
labels:
  - automation
  - infrastructure
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
We have chain2 (2 guard+modify pairs) and chain3 (3 pairs). rb_push needs 8+ pairs. Instead of writing chain4, chain5, ..., chain8, write a general N-step chain using a list of guard/modify pairs and recursion. Or: write chain4 and chain5 (the max practical nesting before kernel depth), then compose chain5 with chain3 for 8-step. The L1_seq_modify_modify approach (fusing into one modify) is the alternative — define the composed function f = fN ∘ ... ∘ f1 explicitly and prove one guard_modify_fused for the whole chain.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Either: chainN for arbitrary N, or chain4+chain5 for practical coverage
- [x] #2 rb_push's 8-step chain expressible using these lemmas
- [x] #3 All chain lemmas proven with zero sorry
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Add L1_hoare_guard_modify_chain4: peel guard+modify, delegate to chain3
2. Add L1_hoare_guard_modify_chain5: peel guard+modify, delegate to chain4
3. Add L1_hoare_guard_modify_compose: composition lemma combining two chain results
4. Build and verify zero sorry
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
L1_guard_modify_guard_modify_result proven (chains 2 guard+modify pairs). In git stash. Also L1_condition_modify_skip_guard_modify_result proven for condition+modify/skip followed by guard+modify. The broken L1_condition_modify_throw_skip_guard_modify_result needs a different approach to unfold L1.condition — use L1_elim_cond_true/false pattern from Sel4CapProof instead of simp/dsimp.

Added chain4, chain5, composition lemma, and primed variants.
All lemmas fully proven, build passes with zero sorry.

rb_push 8-step chain: use L1_hoare_guard_modify_chain_compose with chain5' for first 5 + chain3 for remaining 3. The primed variants produce the r=ok∧R form needed by the compose lemma.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Added chain4, chain5, chain_compose, chain_compose', and primed variants (chain2'-chain5') to L1HoareRules.lean. All proven, zero sorry. rb_push's 8-step chain can use chain5'+chain3. Arbitrary N via nested compose.
<!-- SECTION:FINAL_SUMMARY:END -->
