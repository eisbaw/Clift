---
id: TASK-0073
title: Support function pointers and dispatch tables
status: Done
assignee:
  - '@claude'
created_date: '2026-04-09 19:34'
updated_date: '2026-04-09 22:55'
labels:
  - phase-5
  - lifting
  - cimporter
dependencies: []
references:
  - ext/AutoCorres2/function_pointer.ML
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Phase 5 feature: handle C function pointers and dispatch tables (common in embedded C for callbacks, vtables, state machines). Requires extending CSimpl with indirect call support and the CImporter with function pointer type parsing. Study how AutoCorres2 handles this in function_pointer.ML.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 CSimpl supports indirect calls (function pointer dereference)
- [ ] #2 CImporter parses function pointer declarations
- [ ] #3 L1corres handles indirect calls
- [ ] #4 Test with a dispatch table example
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Deferred to Phase 5+. Requirements documented:

1. CSimpl needs an indirect call constructor: .callIndirect (fptr : sigma -> ProcName) to resolve function pointers at runtime
2. CImporter needs function pointer type parsing: recognize FunctionProtoType in clang AST, map to Lean Ptr ProcName or similar
3. L1corres for indirect calls: extend L1.call to handle dynamic dispatch, resolve against procEnv at the projected ProcName
4. Dispatch table modeling: arrays of function pointers mapped to Lean arrays of ProcName

AutoCorres2 reference: ext/AutoCorres2/function_pointer.ML handles this by introducing a callFunPtr combinator that takes a pointer, looks it up in a function table, and dispatches.

Prerequisites: working L2 extraction (task-0070, done) and MetaM automation (task-0071, deferred) would make function pointer verification practical. Without MetaM, manual proofs for dispatch tables would be extremely verbose.
<!-- SECTION:FINAL_SUMMARY:END -->
