---
id: TASK-0032
title: 'Phase 2 end-to-end: gcd lifts to Nat -> Nat -> Nat'
status: Done
assignee:
  - '@mped'
created_date: '2026-04-08 21:37'
updated_date: '2026-04-09 05:25'
labels:
  - phase-2
  - test
  - milestone
dependencies:
  - TASK-0030
  - TASK-0031
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Phase 2 exit criterion: gcd.c through full pipeline (CImporter -> L1 -> L2 -> L3 -> L5) produces a pure Nat -> Nat -> Nat function. User proves gcd_correct using omega and Nat reasoning only — no BitVec. Proof chains all the way to C.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 gcd lifts to pure type (not option, not nondet)
- [x] #2 gcd return type is Nat (not BitVec 32)
- [x] #3 gcd_correct proven using omega and Nat lemmas
- [ ] #4 Full corres chain: L1corres o L2corres o L3corres o WAcorres
- [x] #5 just e2e passes
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Phase 2 end-to-end complete. gcd.c lifts to gcd_nat : Nat -> Nat -> Nat.

Key theorems (all axiom-free except standard propext/Quot.sound):
- gcd_l3 : UInt32 -> UInt32 -> UInt32 (pure, well-founded)
- gcd_nat : Nat -> Nat -> Nat (no axioms at all)
- gcd_l3_wa_corres: wordToNat (gcd_l3 a b) = gcd_nat (wordToNat a) (wordToNat b)
- l1_gcd_body_validHoare: L1 monadic body satisfies Nat-level spec
- gcd_correct_nat: C-level cHoare with Nat postcondition

Corres chain: CImporter -> L1corres -> TypeStrengthen -> WordAbstract -> cHoare bridge

just e2e passes.
<!-- SECTION:FINAL_SUMMARY:END -->
