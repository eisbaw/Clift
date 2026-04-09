---
id: TASK-0038
title: 'CImporter: handle struct definitions and field access'
status: Done
assignee:
  - '@mped'
created_date: '2026-04-08 21:38'
updated_date: '2026-04-09 17:10'
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
- [x] #1 Parses struct definitions from clang JSON
- [x] #2 Generates Lean 4 structure for each C struct
- [x] #3 Generates CType/MemType instances with correct size/alignment
- [x] #4 s.field emits field projection
- [x] #5 p->field emits pointer deref + field projection
- [x] #6 test/c_sources/list_length.c imports correctly
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
CImporter struct support:
- Parses RecordDecl from clang JSON, creates StructDef with computed layout
- Generates Lean 4 structure (C_<name>) with CType/MemType instances
- Handles struct pointer types (struct node *) with forward references
- s.field emits field projection, p->field emits hVal + field projection
- p->field write: read-modify-write pattern with heapPtrValid guard
- Pointer-vs-NULL comparisons emit Ptr.null instead of literal 0
- Signed int types mapped to UInt at memory level (bit patterns identical)
- Fixed Ptr DecidableEq to not require DecidableEq of phantom type parameter
- list_length.c imports correctly and compiles (struct node: size=16, align=8)
- 53 Python tests pass, all Lean code builds (51 jobs)
- One sorry: struct roundtrip proof (generated, to be mechanized later)
<!-- SECTION:FINAL_SUMMARY:END -->
