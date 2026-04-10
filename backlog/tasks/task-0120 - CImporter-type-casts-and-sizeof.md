---
id: TASK-0120
title: 'CImporter: type casts and sizeof'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-10 15:29'
updated_date: '2026-04-10 17:40'
labels:
  - phase-g
  - cimporter
  - industrial
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
C code uses casts (explicit and implicit) and sizeof constantly. Need: (1) CStyleCastExpr and ImplicitCastExpr from clang JSON — identify widening (safe), narrowing (lossy), sign change, (2) emit appropriate conversion with guards for narrowing/sign change, (3) sizeof(type) and sizeof(expr) — emit as compile-time constant using CType.size. Without casts: can't handle most real C. Without sizeof: can't handle malloc/memcpy/array sizing.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Explicit casts parsed (CStyleCastExpr)
- [x] #2 Implicit casts handled (widening: zero-extend, sign-extend)
- [x] #3 Narrowing casts emit guard (value fits in target type)
- [x] #4 sizeof(type) emitted as CType.size constant
- [x] #5 sizeof(expr) emitted as CType.size of expr's type
- [x] #6 Test: C function with mixed-width arithmetic and casts
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Modify _parse_expr to handle CStyleCastExpr properly (extract target/source types)
2. In lean_emitter, emit appropriate conversion:
   - Widening (small -> large): identity (zero extend happens automatically in UInt)
   - Narrowing (large -> small): emit guard + truncation
   - Sign change: emit guard
3. Handle UnaryExprOrTypeTraitExpr for sizeof
4. Create test/c_sources/casts_sizeof.c
5. Verify generated .lean compiles
<!-- SECTION:PLAN:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Implemented type casts and sizeof in CImporter.

Changes:
- ast_parser.py: CStyleCastExpr now extracts source/target types and emits cast_expr nodes (not pass-through). UnaryExprOrTypeTraitExpr parsed for sizeof(type) and sizeof(expr).
- lean_emitter.py: cast_expr emission with .toNat.toUIntN conversion. Narrowing casts get guards (value < 2^target_bits). Sizeof emits compile-time constant from type_size_align.
- Fixed ret__val field naming for multi-return-type programs (new _ret_field_name and _callee_ret_field helpers).
- Test: test/c_sources/casts_sizeof.c with widening, narrowing, sizeof, mixed-width.
- Generated/CastsSizeof.lean compiles successfully.
- All 82 existing Python tests pass.
<!-- SECTION:FINAL_SUMMARY:END -->
