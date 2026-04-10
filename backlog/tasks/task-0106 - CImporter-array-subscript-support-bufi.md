---
id: TASK-0106
title: 'CImporter: array subscript support (buf[i])'
status: To Do
assignee: []
created_date: '2026-04-10 12:58'
labels:
  - critical-path
  - cimporter
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Real C uses arrays extensively. Our CImporter cannot handle ArraySubscriptExpr. Need: (1) parse buf[i] from clang JSON, (2) emit as pointer arithmetic *(base + i * sizeof(elem)), (3) generate bounds-check guard (i < array_size), (4) handle array declarations (local arrays, struct array fields). seL4 uses arrays for page tables, capability tables, thread queues — this is essential for real embedded C.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 CImporter parses ArraySubscriptExpr from clang JSON
- [ ] #2 Emits pointer arithmetic: *(base + i * sizeof(elem))
- [ ] #3 Bounds-check guard generated
- [ ] #4 Local array declarations handled
- [ ] #5 Struct fields that are arrays handled
- [ ] #6 Test: C function that sums array elements
<!-- AC:END -->
