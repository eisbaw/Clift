---
id: TASK-0001
title: 'Define CResult, CError, and NondetM types'
status: To Do
assignee: []
created_date: '2026-04-08 21:33'
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
- [ ] #1 CResult inductive with ok and fail constructors compiles
- [ ] #2 CError inductive covers undefinedBehavior, overflow, nullDeref
- [ ] #3 NondetM structure with run field compiles
- [ ] #4 NondetM Monad instance (pure, bind) implemented and compiles
- [ ] #5 fail, get, put, modify helpers defined
<!-- AC:END -->
