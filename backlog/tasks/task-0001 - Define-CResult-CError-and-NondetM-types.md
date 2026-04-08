---
id: TASK-0001
title: 'Define CResult, CError, and NondetM types'
status: Done
assignee:
  - '@mped'
created_date: '2026-04-08 21:33'
updated_date: '2026-04-08 22:34'
labels:
  - phase-0
  - monadlib
dependencies: []
references:
  - ext/AutoCorres2/L1Defs.thy
  - Clift/MonadLib/NondetM.lean
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Define the foundational monad types: CResult (ok/fail), CError (UB, overflow, null deref), and NondetM (nondeterministic state monad with failure). NondetM.run : σ → { results : Set (α × σ) // failed : Bool }. Follow seL4's nondet_monad structure.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 CResult inductive with ok and fail constructors compiles
- [x] #2 CError inductive covers undefinedBehavior, overflow, nullDeref
- [x] #3 NondetM structure with run field compiles
- [x] #4 NondetM Monad instance (pure, bind) implemented and compiles
- [x] #5 fail, get, put, modify helpers defined
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
All types defined and compile. Used Prop for failure flag (not Bool) since NondetM is never evaluated. Used set-builder notation for bind results instead of iUnion. Guard requires DecidablePred.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Defined CResult (ok/fail), CError (undefinedBehavior, overflow, nullDeref), NondetResult (results set + failed Prop), and NondetM (sigma -> NondetResult) in Clift/MonadLib/NondetM.lean. Implemented Monad instance (pure, bind), plus fail, get, put, modify, guard, select, condition helpers. Added simp lemmas for all run operations. Used Prop (not Bool) for failure flag since NondetM is never evaluated. Also defined WhileResult/WhileFail inductive predicates and whileLoop, plus skip/basic/seq/cond combinators.
<!-- SECTION:FINAL_SUMMARY:END -->
