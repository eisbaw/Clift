---
id: TASK-0071
title: 'CVcg tactic: MetaM-level implementation for flat proof terms'
status: To Do
assignee: []
created_date: '2026-04-09 19:34'
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
