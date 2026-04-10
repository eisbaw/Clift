---
id: TASK-0080
title: 'MetaM L1 SimplConv: auto-convert CSimpl to L1 monadic form'
status: To Do
assignee: []
created_date: '2026-04-10 05:17'
labels:
  - phase-a
  - metam
  - automation
dependencies: []
references:
  - ext/AutoCorres2/simpl_conv.ML
  - ext/AutoCorres2/SimplConv.thy
  - Clift/Lifting/SimplConv.lean
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Port AutoCorres2's simpl_conv.ML to Lean 4 MetaM. Given a CSimpl function body, automatically generate the L1 monadic equivalent + L1corres proof. Must handle all CSimpl constructors: skip, basic, seq, cond, while, guard, throw, catch, dynCom, spec, call. The MetaM walks the CSimpl term structurally, emitting L1 combinators and assembling the L1corres proof from per-constructor lemmas. Currently this is manual (Examples/GcdProof.lean). Target: one command lifts all functions in a Generated/*.lean file.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 MetaM command 'clift_l1' converts any CSimpl function to L1 form
- [ ] #2 L1corres proof generated automatically for each function
- [ ] #3 Handles all 11 CSimpl constructors
- [ ] #4 Tested on gcd, swap, rotate3, abs_diff, clamp — all automated
- [ ] #5 No sorry in any generated proof
- [ ] #6 Performance: <5s per function
<!-- AC:END -->
