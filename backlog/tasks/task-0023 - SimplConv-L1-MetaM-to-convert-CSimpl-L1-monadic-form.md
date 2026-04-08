---
id: TASK-0023
title: 'SimplConv (L1): MetaM to convert CSimpl -> L1 monadic form'
status: To Do
assignee: []
created_date: '2026-04-08 21:36'
labels:
  - phase-1
  - lifting
  - metam
dependencies:
  - TASK-0022
  - TASK-0014
references:
  - ext/AutoCorres2/simpl_conv.ML
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Write the Lean 4 metaprogram that walks a CSimpl term and produces the L1 monadic equivalent + an L1corres proof. Each CSimpl constructor maps to a monadic combinator. The proof is assembled from per-constructor L1corres lemmas. Study ext/AutoCorres2/simpl_conv.ML for the Isabelle implementation.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 MetaM program converts CSimpl.skip to pure () with corres proof
- [ ] #2 MetaM program converts CSimpl.basic to state update with corres proof
- [ ] #3 MetaM program converts CSimpl.seq to bind with corres proof
- [ ] #4 MetaM program converts CSimpl.cond to if-then-else with corres proof
- [ ] #5 MetaM program converts CSimpl.while to monadic loop with corres proof
- [ ] #6 All generated proofs kernel-checked, no sorry
<!-- AC:END -->
