---
id: TASK-0106
title: 'CImporter: array subscript support (buf[i])'
status: In Progress
assignee:
  - '@claude'
created_date: '2026-04-10 12:58'
updated_date: '2026-04-10 13:31'
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
- [x] #1 CImporter parses ArraySubscriptExpr from clang JSON
- [x] #2 Emits pointer arithmetic: *(base + i * sizeof(elem))
- [x] #3 Bounds-check guard generated
- [ ] #4 Local array declarations handled
- [ ] #5 Struct fields that are arrays handled
- [x] #6 Test: C function that sums array elements
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Add ArraySubscriptExpr parsing in ast_parser.py
2. Add array_subscript Expr kind
3. Emit as pointer arithmetic: hVal heap (Ptr.offset base index)
4. Add Ptr.offset to CSemantics.lean
5. Generate bounds guard for array access
6. Handle array type declarations
7. Write test C file sum_array.c
8. Test import and lake build
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
- ArraySubscriptExpr parsed from clang JSON
- Emits Ptr.elemOffset for array index computation
- heapPtrValid guard generated for array reads
- array_write statement kind added for arr[i] = val
- Ptr.addBytes and Ptr.elemOffset added to CSemantics
- sum_array.c test compiles in Lean
- AC#4 (local array decls) and AC#5 (struct array fields) deferred
<!-- SECTION:NOTES:END -->
