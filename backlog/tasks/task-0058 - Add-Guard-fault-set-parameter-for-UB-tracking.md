---
id: TASK-0058
title: Add Guard fault-set parameter for UB tracking
status: To Do
assignee: []
created_date: '2026-04-08 22:55'
labels:
  - enhancement
  - csemantics
dependencies: []
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Simpl's Guard constructor takes a fault-set parameter f that identifies WHICH guard failed. Our guard just produces a plain fault with no identifier. Not needed for soundness but useful for debugging and error reporting. Low priority for Phase 0.
<!-- SECTION:DESCRIPTION:END -->
