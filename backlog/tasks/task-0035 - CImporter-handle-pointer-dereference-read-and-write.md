---
id: TASK-0035
title: 'CImporter: handle pointer dereference read and write'
status: To Do
assignee: []
created_date: '2026-04-08 21:37'
labels:
  - phase-3a
  - cimporter
dependencies:
  - TASK-0034
references:
  - test/c_sources/swap.c
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Extend CImporter to handle pointer dereference: *p (read) and *p = val (write). These emit CSimpl.guard (pointer valid) followed by CSimpl.basic (heap read/write). Test with swap.c.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Pointer read (*p) emits guard + basic with hVal
- [ ] #2 Pointer write (*p = v) emits guard + basic with heapUpdate
- [ ] #3 Null pointer dereference guarded (guard for p != NULL)
- [ ] #4 test/c_sources/swap.c imports correctly
- [ ] #5 Generated/Swap.lean compiles
<!-- AC:END -->
