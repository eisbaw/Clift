---
id: TASK-0105
title: 'MetaM VCG: flat proof term generation for multi-step L1 programs'
status: To Do
assignee: []
created_date: '2026-04-10 12:58'
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
