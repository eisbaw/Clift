---
id: TASK-0029
title: 'WordAbstract (L5): define word-to-integer abstraction'
status: To Do
assignee: []
created_date: '2026-04-08 21:36'
labels:
  - phase-2
  - lifting
dependencies:
  - TASK-0025
references:
  - ext/AutoCorres2/WordAbstract.thy
  - ext/AutoCorres2/word_abstract.ML
  - Clift/Lifting/WordAbstract.lean
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Define the abstraction from BitVec n to Int/Nat with range guards. When BitVec 32 is used for unsigned values, abstract to Nat with 0 <= n < 2^32 guard. When used for signed, abstract to Int with range guard. Define WA corres. Leverage Mathlib's BitVec library and omega tactic.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Unsigned word abstraction: BitVec n -> Nat with range guard defined
- [ ] #2 Signed word abstraction: BitVec n -> Int with range guard defined
- [ ] #3 wa_corres relation defined connecting word-level and int-level execution
- [ ] #4 Basic lemmas: if in range, BitVec.toNat roundtrips (proven with omega)
<!-- AC:END -->
