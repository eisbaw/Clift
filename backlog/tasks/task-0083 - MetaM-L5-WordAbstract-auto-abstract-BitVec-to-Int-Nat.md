---
id: TASK-0083
title: 'MetaM L5 WordAbstract: auto-abstract BitVec to Int/Nat'
status: To Do
assignee: []
created_date: '2026-04-10 05:17'
labels:
  - phase-a
  - metam
  - automation
dependencies:
  - TASK-0082
references:
  - ext/AutoCorres2/word_abstract.ML
  - ext/AutoCorres2/WordAbstract.thy
  - Clift/Lifting/WordAbstract.lean
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Port AutoCorres2's word_abstract.ML to Lean 4 MetaM. Given an L3 function using BitVec/UInt types, replace with Int/Nat + range guards. Generate WAcorres proof. Leverage Mathlib-free BitVec lemmas we already have (Clift/Lifting/WordAbstract.lean). Currently manual (Examples/GcdWordAbstract.lean).
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 MetaM command 'clift_wa' abstracts words for each function
- [ ] #2 UInt32 -> Nat for unsigned, Int for signed
- [ ] #3 Range guards generated
- [ ] #4 WAcorres proof generated automatically
- [ ] #5 gcd lifts to Nat -> Nat -> Nat
- [ ] #6 No sorry
<!-- AC:END -->
