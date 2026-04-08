---
id: TASK-0003
title: 'Define Hoare triples: validHoare and totalHoare'
status: To Do
assignee: []
created_date: '2026-04-08 21:33'
labels:
  - phase-0
  - monadlib
dependencies:
  - TASK-0001
references:
  - Clift/MonadLib/Hoare.lean
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Define partial correctness (validHoare) and total correctness (totalHoare) Hoare triples over NondetM. totalHoare = validHoare + termination (results nonempty). Follow plan.md Decision 6.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 validHoare definition compiles and matches plan.md spec
- [ ] #2 totalHoare definition compiles: validHoare + Nonempty results
- [ ] #3 Basic sanity lemma: validHoare True (pure x) (fun r _ => r = x) proven
<!-- AC:END -->
