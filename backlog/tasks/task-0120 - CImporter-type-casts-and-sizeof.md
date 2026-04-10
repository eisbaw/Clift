---
id: TASK-0120
title: 'CImporter: type casts and sizeof'
status: To Do
assignee: []
created_date: '2026-04-10 15:29'
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
- [ ] #1 Explicit casts parsed (CStyleCastExpr)
- [ ] #2 Implicit casts handled (widening: zero-extend, sign-extend)
- [ ] #3 Narrowing casts emit guard (value fits in target type)
- [ ] #4 sizeof(type) emitted as CType.size constant
- [ ] #5 sizeof(expr) emitted as CType.size of expr's type
- [ ] #6 Test: C function with mixed-width arithmetic and casts
<!-- AC:END -->
