---
id: TASK-0030
title: 'WordAbstract (L5): MetaM to replace BitVec with Int/Nat'
status: To Do
assignee: []
created_date: '2026-04-08 21:36'
labels:
  - phase-2
  - lifting
  - metam
dependencies:
  - TASK-0029
  - TASK-0028
references:
  - ext/AutoCorres2/word_abstract.ML
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Write MetaM that transforms L3 functions by replacing BitVec operations with Int/Nat operations + range guards. Generate WAcorres proofs. Study word_abstract.ML. Lean 4 advantage: Mathlib's BitVec lemmas + omega should handle most proof obligations automatically.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 MetaM replaces BitVec 32 arithmetic with Nat arithmetic + guards
- [ ] #2 WAcorres proof generated for each function
- [ ] #3 omega closes range-checking obligations
- [ ] #4 gcd.c: lifts to Nat -> Nat -> Nat (pure, no BitVec)
<!-- AC:END -->
