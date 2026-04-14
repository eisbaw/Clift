---
id: TASK-0264
title: 'Update README.md: stale sorry count (says 27, actual 42) and stale task count'
status: To Do
assignee: []
created_date: '2026-04-14 20:53'
updated_date: '2026-04-14 20:56'
labels:
  - docs
  - stale
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
README.md Status section has stale numbers. Sorry count says 27 but actual is 17 (per Python audit). Task done count says 215+ but is higher. Also ring_buffer_ext refinement says 21/40 which may be outdated.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Sorry count matches just sorry-count output
- [ ] #2 Task done count matches backlog task list -s Done count
- [ ] #3 Refinement progress matches actual RBExtRefinement state
<!-- AC:END -->
