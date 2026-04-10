---
id: TASK-0187
title: 'Backlog dependency map: explicit task ordering and blocking relationships'
status: To Do
assignee: []
created_date: '2026-04-10 18:55'
labels:
  - meta
  - planning
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
This audit identified multiple dependency gaps: TASK-0135 (soundness) should block TASK-0136-0139, TASK-0142 (Exec audit) should block TASK-0164 (concurrency), TASK-0167 (ASM) should block TASK-0164 (interrupt model needs ASM primitives), TASK-0166 (regression) should block TASK-0156 (seL4 verification). These dependencies are not captured in the backlog. Need: (1) Review all To Do tasks for dependencies, (2) Add dependency annotations to each task, (3) Identify the critical path, (4) Flag tasks that are blocked but don't declare it. This is a one-time cleanup that prevents wasted work on tasks whose prerequisites are not met.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 All To Do tasks reviewed for dependencies
- [ ] #2 Dependencies documented on each task
- [ ] #3 Critical path identified
- [ ] #4 Blocked tasks flagged
<!-- AC:END -->
