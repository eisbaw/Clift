---
id: TASK-0105
title: 'MetaM VCG: flat proof term generation for multi-step L1 programs'
status: To Do
assignee:
  - '@claude'
created_date: '2026-04-10 12:58'
updated_date: '2026-04-14 22:12'
labels:
  - critical-path
  - metam
  - scalability
dependencies: []
references:
  - ext/AutoCorres2/autocorres.ML
  - Examples/SwapProof.lean
  - Clift/Lifting/L1HoareRules.lean
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The single biggest bottleneck. Every validHoare proof for 10+ step programs requires manual L1 combinator tracing. Need a MetaM-level VCG that generates FLAT proof terms using the [local irreducible] hVal/heapUpdate trick. The VCG walks the L1 computation, at each step: (1) unfold one combinator, (2) apply the matching L1 Hoare rule, (3) emit a projection simp lemma for the state transform, (4) discharge the guard/modify obligations. The proof term must stay at bounded depth regardless of program length. Study ext/AutoCorres2/autocorres.ML for the Isabelle equivalent. This is the task that unlocks seL4-scale verification — without it, Claude writes ~200 lines of mechanical proof per function.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 MetaM VCG handles L1.seq chains of 20+ steps
- [ ] #2 Generates [local irreducible] + projection simp lemmas per step automatically
- [ ] #3 swap validHoare proven fully automatically (no sorry, no manual steps)
- [ ] #4 ring_buffer push validHoare proven automatically
- [ ] #5 Proof terms stay at bounded kernel depth regardless of program length
- [ ] #6 Performance: <10s per function for 50-step programs
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Create Clift/Tactics/L1Vcg.lean with a MetaM tactic
2. Walk the L1 term structure in MetaM
3. At each L1.modify: extract lambda body, generate projection lemmas with local irreducible
4. At each L1.guard: extract predicate, chain with L1_guard_modify_result
5. At each L1.seq: apply L1_seq_singleton_ok
6. At L1.catch: apply L1_catch_singleton_ok
7. Test on swap (7 steps)
8. Ensure proof terms stay at bounded depth
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
- Created Clift/Tactics/L1Vcg.lean with l1_vcg, l1_vcg_all, l1_vcg_simp, l1_vcg_finish tactics
- Tactics apply L1 Hoare rules (guard, modify, seq_ok, catch_ok, skip)
- Verified on swap step characterization (L1_guard_modify_result)
- Key limitation: Lean higher-order unifier cannot infer intermediate conditions R
  when postcondition involves complex structure updates
- The SwapProof.lean results-level approach remains the working pattern
- Full MetaM VCG for automatic R inference deferred (requires weakest precondition computation)
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Partially completed. L1Vcg.lean tactic created with l1_vcg/l1_vcg_all/l1_vcg_finish. Works for simple programs. Cannot fully automate 7+ step programs due to Lean unifier not inferring intermediate conditions. The SwapProof.lean results-level approach (L1_guard_modify_result + L1_seq_singleton_ok + L1_catch_singleton_ok with [local irreducible]) remains the working pattern. A MetaM wp-computation tactic that works backwards from postcondition is the remaining work.
<!-- SECTION:FINAL_SUMMARY:END -->
