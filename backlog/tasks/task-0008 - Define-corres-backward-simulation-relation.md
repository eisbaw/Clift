---
id: TASK-0008
title: Define corres (backward simulation) relation
status: To Do
assignee: []
created_date: '2026-04-08 21:34'
labels:
  - phase-0
  - monadlib
dependencies:
  - TASK-0001
references:
  - ext/AutoCorres2/CorresXF.thy
  - Clift/MonadLib/Corres.lean
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Define the correspondence/refinement relation following seL4's corres_underlying. Must use backward simulation: for every concrete result, abstract has a matching one. Include state relation, no-fail flags, return value relation, and guard preconditions. This is the most critical definition — get it wrong and everything downstream is unsound.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 corres definition matches plan.md Decision 1 exactly
- [ ] #2 Backward simulation direction verified: concrete results imply abstract results
- [ ] #3 State relation, no-fail flags, return relation, guards all present
- [ ] #4 Sanity test: corres Id true true Eq True True (pure x) (pure x) proven trivially
<!-- AC:END -->
