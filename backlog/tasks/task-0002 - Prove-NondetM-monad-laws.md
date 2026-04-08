---
id: TASK-0002
title: Prove NondetM monad laws
status: To Do
assignee: []
created_date: '2026-04-08 21:33'
labels:
  - phase-0
  - monadlib
dependencies:
  - TASK-0001
references:
  - ext/AutoCorres2/L1Defs.thy
  - Clift/MonadLib/NondetM.lean
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Prove bind_assoc, pure_bind, bind_pure for NondetM. These are foundational — every subsequent proof depends on the monad laws being correct. Use ext to verify against seL4's monad law proofs.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 bind_assoc theorem proven and kernel-checked
- [ ] #2 pure_bind theorem proven and kernel-checked
- [ ] #3 bind_pure theorem proven and kernel-checked
- [ ] #4 All proofs use no sorry
<!-- AC:END -->
