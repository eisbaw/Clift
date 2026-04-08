---
id: TASK-0053
title: Remove dead CError/CResult types from NondetM.lean
status: To Do
assignee: []
created_date: '2026-04-08 22:39'
labels:
  - cleanup
  - monadlib
dependencies: []
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
CError and CResult types are defined in NondetM.lean but never used. NondetM uses Prop-based failure, not typed errors. Remove the dead code to avoid confusion.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 CError and CResult removed from NondetM.lean
- [ ] #2 lake build Clift succeeds after removal
<!-- AC:END -->
