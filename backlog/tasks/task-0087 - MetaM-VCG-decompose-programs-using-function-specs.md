---
id: TASK-0087
title: 'MetaM VCG: decompose programs using function specs'
status: To Do
assignee: []
created_date: '2026-04-10 05:17'
labels:
  - phase-b
  - metam
  - tactics
dependencies:
  - TASK-0086
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Build a MetaM-level VCG that decomposes validHoare goals into leaf obligations. Must use function specs at call sites (not inline bodies). Must generate FLAT proof terms using the [local irreducible] hVal/heapUpdate pattern to avoid kernel depth issues. This replaces the current macro-based c_vcg. Study ext/AutoCorres2/autocorres.ML for the Isabelle equivalent. Key requirements: handle seq, cond, while (with user-supplied invariant), call (via spec), guard, modify.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 MetaM VCG decomposes validHoare goals into leaf subgoals
- [ ] #2 Uses function specs at call sites (not body inlining)
- [ ] #3 Generates flat proof terms (no kernel depth issue)
- [ ] #4 While loops: requires user-supplied invariant, generates invariant obligations
- [ ] #5 Tested on swap (7 steps) — fully automated
- [ ] #6 Tested on a caller that invokes a verified callee
- [ ] #7 No sorry
<!-- AC:END -->
