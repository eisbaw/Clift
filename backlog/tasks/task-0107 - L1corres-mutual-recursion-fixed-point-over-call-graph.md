---
id: TASK-0107
title: 'L1corres mutual recursion: fixed-point over call graph'
status: To Do
assignee: []
created_date: '2026-04-10 12:58'
labels:
  - critical-path
  - lifting
dependencies: []
references:
  - ext/AutoCorres2/simpl_conv.ML
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
When functions call each other (A calls B, B calls C), L1corres proofs are mutually dependent. Currently clift_l1 skips corres for call-containing functions. Need a fixed-point construction: prove L1corres for ALL functions simultaneously by well-founded induction on the call graph. seL4 does this via a recursive lemma that assumes corres for callees at smaller depth. Study ext/AutoCorres2/simpl_conv.ML for the approach.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Call graph extracted from ProcEnv
- [ ] #2 L1corres proved for mutually-recursive function sets
- [ ] #3 Direct recursion (f calls f) handled
- [ ] #4 Mutual recursion (f calls g, g calls f) handled
- [ ] #5 clift_l1 generates corres proofs for call-containing functions
- [ ] #6 Tested on multi_call.c (5 functions with calls)
<!-- AC:END -->
