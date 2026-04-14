---
id: TASK-0029
title: 'WordAbstract (L5): define word-to-integer abstraction'
status: Done
assignee:
  - '@mped'
created_date: '2026-04-08 21:36'
updated_date: '2026-04-09 05:03'
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
- [x] #1 Unsigned word abstraction: BitVec n -> Nat with range guard defined
- [ ] #2 Signed word abstraction: BitVec n -> Int with range guard defined
- [x] #3 wa_corres relation defined connecting word-level and int-level execution
- [x] #4 Basic lemmas: if in range, BitVec.toNat roundtrips (proven with omega)
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Defined word abstraction in Clift/Lifting/WordAbstract.lean. wordToNat/natToWord with roundtrip proofs. Arithmetic lemmas: mod (unconditional), add (with range guard), zero, eq/ne. WAcorres_pure2 defined for binary pure function correspondence. Signed abstraction deferred (not needed for gcd). All proofs kernel-checked, zero sorry.
<!-- SECTION:FINAL_SUMMARY:END -->
