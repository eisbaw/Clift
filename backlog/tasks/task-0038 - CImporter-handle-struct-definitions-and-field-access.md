---
id: TASK-0038
title: 'CImporter: handle struct definitions and field access'
status: To Do
assignee: []
created_date: '2026-04-08 21:38'
labels:
  - phase-3b
  - cimporter
dependencies:
  - TASK-0037
references:
  - ext/AutoCorres2/c-parser/
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Extend CImporter for structs: parse struct definitions, generate Lean 4 structure types with CType/MemType instances, handle field access (s.field and p->field). Generate correct field offset calculations. Test with list_length.c (struct node).
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Parses struct definitions from clang JSON
- [ ] #2 Generates Lean 4 structure for each C struct
- [ ] #3 Generates CType/MemType instances with correct size/alignment
- [ ] #4 s.field emits field projection
- [ ] #5 p->field emits pointer deref + field projection
- [ ] #6 test/c_sources/list_length.c imports correctly
<!-- AC:END -->
