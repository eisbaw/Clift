---
id: TASK-0022
title: 'SimplConv (L1): define L1 monad type and L1corres'
status: Done
assignee:
  - '@mped'
created_date: '2026-04-08 21:36'
updated_date: '2026-04-08 23:54'
labels:
  - phase-1
  - lifting
dependencies:
  - TASK-0010
  - TASK-0001
references:
  - ext/AutoCorres2/SimplConv.thy
  - ext/AutoCorres2/L1Defs.thy
  - Clift/Lifting/SimplConv.lean
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Define the L1 monad type (NondetM over full CState) and the L1corres relation connecting CSimpl.Exec to L1 monadic execution. L1corres states: if the CSimpl program executes to outcome o, the L1 monadic version produces matching results. Study ext/AutoCorres2/SimplConv.thy and L1Defs.thy.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 L1 monad type defined (NondetM CState α)
- [x] #2 L1corres relation defined connecting Exec to NondetM execution
- [x] #3 L1corres correctly handles all Outcome cases (normal, abrupt, fault)
- [x] #4 Basic L1corres lemmas for skip and basic proven
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
L1Monad defined as NondetM σ (Except Unit Unit).
L1corres defined with three conjuncts (normal/abrupt/fault).
Basic lemmas (skip, basic, throw) proved.
Complex lemmas (seq, cond, catch, guard, while) axiomatized -- proofs tracked in task-0061.
L1outcomeMatch helper not needed -- used explicit conjuncts instead.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Defined L1Monad as NondetM σ (Except Unit Unit) and L1corres connecting CSimpl Exec to L1 monadic execution. Proved L1corres for skip, basic, throw. Complex constructor lemmas (seq, cond, catch, guard, while) stated as axioms pending proof (task-0061). Created ADR-001 documenting the exception encoding decision.
<!-- SECTION:FINAL_SUMMARY:END -->
