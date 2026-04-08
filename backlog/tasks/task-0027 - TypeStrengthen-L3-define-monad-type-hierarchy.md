---
id: TASK-0027
title: 'TypeStrengthen (L3): define monad type hierarchy'
status: To Do
assignee: []
created_date: '2026-04-08 21:36'
labels:
  - phase-2
  - lifting
dependencies:
  - TASK-0025
references:
  - ext/AutoCorres2/TypeStrengthen.thy
  - ext/AutoCorres2/monad_types.ML
  - Clift/Lifting/TypeStrengthen.lean
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Define the 3 monad levels for TypeStrengthen: pure (no state, no failure), option (may fail), nondet (full). Define the injection/coercion from each into NondetM. Define ts_rule attribute for registering strengthening rewrite rules. Study ext/AutoCorres2/TypeStrengthen.thy and monad_types.ML.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 pure, option, nondet monad types defined
- [ ] #2 Injection from pure -> NondetM proven correct
- [ ] #3 Injection from option -> NondetM proven correct
- [ ] #4 ts_rule mechanism defined (even if simple pattern matching for now)
<!-- AC:END -->
