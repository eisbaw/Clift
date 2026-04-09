---
id: TASK-0078
title: 'Performance: incremental re-verification when C changes'
status: To Do
assignee: []
created_date: '2026-04-09 19:34'
labels:
  - phase-5
  - performance
dependencies: []
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Currently, any change to a .c file requires re-running the entire pipeline. For large codebases, need incremental re-verification: only re-check functions that changed and their dependents. Requires: dependency tracking between functions, caching of intermediate proof states, and integration with Lake's build system.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Changed functions detected automatically
- [ ] #2 Only affected proofs re-checked
- [ ] #3 Cache of intermediate states implemented
- [ ] #4 Measured speedup on a multi-function file
<!-- AC:END -->
