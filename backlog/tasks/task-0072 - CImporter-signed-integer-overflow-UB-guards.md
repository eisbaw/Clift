---
id: TASK-0072
title: 'CImporter: signed integer overflow UB guards'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-09 19:34'
updated_date: '2026-04-09 20:39'
labels:
  - phase-5
  - cimporter
  - tcb
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Currently the CImporter only handles unsigned types (wrapping semantics, no UB). Signed integer overflow is undefined behavior in C. The importer must emit CSimpl.guard nodes for every signed arithmetic operation checking the result is in [INT_MIN, INT_MAX]. This is in the TCB — missing guards mean we verify the wrong semantics.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Signed addition emits guard: INT_MIN <= a + b <= INT_MAX
- [x] #2 Signed subtraction, multiplication similarly guarded
- [x] #3 Signed division guarded for INT_MIN / -1 (UB)
- [x] #4 Test with signed C functions
- [x] #5 No sorry
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
CImporter emits signed overflow guards using UInt32.toBitVec.toInt for signed interpretation. For +/-/*, guard checks INT_MIN <= result <= INT_MAX. For signed division, guard checks not (a == INT_MIN && b == -1). Type propagation via result_type on Expr nodes from clang AST. Test: signed_arith.c generates SignedArith.lean with all guards. No sorry in generated files.
<!-- SECTION:FINAL_SUMMARY:END -->
