---
id: TASK-0056
title: 'Add spec, dynCom, and call monadic combinators to NondetM'
status: To Do
assignee: []
created_date: '2026-04-08 22:39'
labels:
  - monadlib
  - phase-1
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
NondetM is missing combinators needed to map CSimpl constructors in SimplConv: spec (nondeterministic specification via state relation), dynCom (state-dependent computation), and call (procedure call with scope setup/teardown). These are needed for the L1 lifting.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 NondetM.spec combinator defined
- [ ] #2 NondetM.dynCom combinator defined
- [ ] #3 NondetM.call combinator defined matching L1Defs.thy pattern
- [ ] #4 lake build Clift succeeds
<!-- AC:END -->
