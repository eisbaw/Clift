---
id: TASK-0054
title: Remove duplicate condition/cond in NondetM.lean
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
NondetM.condition and NondetM.cond are identical functions (both branch on a state predicate). Remove one to avoid confusion. Keep cond since it matches CSimpl naming.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Only one conditional branching function remains in NondetM
- [ ] #2 All references updated
<!-- AC:END -->
