---
id: TASK-0059
title: 'CImporter: add UB guards for division/modulo by zero'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-08 23:26'
updated_date: '2026-04-09 20:39'
labels:
  - cimporter
  - phase-1
  - ub-guards
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The CImporter does not emit guard nodes for division/modulo-by-zero UB. For gcd, this is safe because the while condition ensures the divisor is nonzero, but for general C code like 'a / b' without a prior check, the importer should emit .guard (fun s => s.locals.b \!= 0) around the operation. Without this, the CSimpl would silently accept division-by-zero as normal execution rather than faulting.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 CImporter emits .guard for / and % operations
- [x] #2 Guard condition checks divisor \!= 0
- [x] #3 Tests cover standalone division without prior conditional
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
CImporter now emits .guard (fun s => divisor != 0) for every / and % operation. Implemented via _collect_div_guards in lean_emitter.py which walks the expression tree. Tests: div_test.c generates DivTest.lean with guards, Gcd.lean now has a guard on a%b. 82 Python tests pass, lake build passes.
<!-- SECTION:FINAL_SUMMARY:END -->
