---
id: TASK-0027
title: 'TypeStrengthen (L3): define monad type hierarchy'
status: Done
assignee:
  - '@mped'
created_date: '2026-04-08 21:36'
updated_date: '2026-04-09 04:53'
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
- [x] #1 pure, option, nondet monad types defined
- [x] #2 Injection from pure -> NondetM proven correct
- [x] #3 Injection from option -> NondetM proven correct
- [x] #4 ts_rule mechanism defined (even if simple pattern matching for now)
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Defined 3 monad levels (pure, option, nondet) in Clift/Lifting/TypeStrengthen.lean. tsLiftPure injects pure values into NondetM (proven no-fail, singleton result). tsLiftOption injects option computations into NondetM (proven correct for both Some/None cases). L3corres_pure and L3corres_option defined as definitional equality. Injection tower: pure embeds into option via pureToOption. All proofs kernel-checked, zero sorry.
<!-- SECTION:FINAL_SUMMARY:END -->
