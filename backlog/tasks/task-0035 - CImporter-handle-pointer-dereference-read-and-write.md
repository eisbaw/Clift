---
id: TASK-0035
title: 'CImporter: handle pointer dereference read and write'
status: Done
assignee:
  - '@mped'
created_date: '2026-04-08 21:37'
updated_date: '2026-04-09 06:01'
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
- [x] #1 Pointer read (*p) emits guard + basic with hVal
- [x] #2 Pointer write (*p = v) emits guard + basic with heapUpdate
- [x] #3 Null pointer dereference guarded (guard for p != NULL)
- [x] #4 test/c_sources/swap.c imports correctly
- [x] #5 Generated/Swap.lean compiles
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Extend c_types.py to support pointer types (uint32_t *)
2. Extend ast_parser.py to handle UnaryOperator * (deref read) and lvalue deref write
3. Extend lean_emitter.py to emit guard + basic for pointer read/write
4. Generate clang JSON for swap.c
5. Run CImporter on swap.c
6. Create Generated/Swap.lean
7. Add Swap to lakefile roots and verify it compiles
8. Update expected snapshots
<!-- SECTION:PLAN:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Extended CImporter to handle pointer dereference (read and write).

Changes:
- c_types.py: CType now supports is_pointer/pointee fields; _parse_pointer_type handles uint32_t* etc.
- ast_parser.py: Expr kind "deref" for *p reads; Stmt kind "deref_write" for *p = v; _extract_deref_target for detecting LHS deref
- lean_emitter.py: deref expressions emit hVal; deref_write emits guard+basic with heapUpdate; _collect_deref_guards recursively finds all pointer reads needing guards
- State.lean: Ptr gets Repr instance; hVal and heapUpdate are now total functions (guard ensures safety)
- Generated/Swap.lean: compiles successfully; swap_body has correct guard structure for all three pointer operations
- All 52 CImporter tests pass; e2e tests pass

CSimpl encoding for swap:
- uint32_t t = *a -> guard(heapPtrValid a) + basic(t := hVal heap a)
- *a = *b -> guard(valid a) + guard(valid b) + basic(heap := heapUpdate heap a (hVal heap b))
- *b = t -> guard(valid b) + basic(heap := heapUpdate heap b t)
<!-- SECTION:FINAL_SUMMARY:END -->
