---
id: TASK-0022
title: 'SimplConv (L1): define L1 monad type and L1corres'
status: To Do
assignee: []
created_date: '2026-04-08 21:36'
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
- [ ] #1 L1 monad type defined (NondetM CState α)
- [ ] #2 L1corres relation defined connecting Exec to NondetM execution
- [ ] #3 L1corres correctly handles all Outcome cases (normal, abrupt, fault)
- [ ] #4 Basic L1corres lemmas for skip and basic proven
<!-- AC:END -->
