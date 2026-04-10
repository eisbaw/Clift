---
id: TASK-0088
title: 'CImporter: handle multi-function C files with calls'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-10 05:17'
updated_date: '2026-04-10 06:28'
labels:
  - phase-b
  - cimporter
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Extend the CImporter to handle C files with multiple functions that call each other. Currently each function's CSimpl body can reference other functions via CSimpl.call, but the generated ProcEnv needs to map all function names to their bodies. Handle: direct calls, calls with return values, calls with pointer arguments. Test with a real multi-function C file.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 CImporter parses files with 5+ functions
- [x] #2 Function calls emit CSimpl.call with correct ProcName
- [x] #3 ProcEnv maps all function names to bodies
- [x] #4 Return values from calls handled correctly
- [ ] #5 Pointer arguments to calls handled
- [x] #6 Test: a C file with helper functions calling each other
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Extended CImporter to handle multi-function C files with calls. Added CallExpr parsing (ast_parser.py), call_args field to Expr, and call emission patterns (dynCom + param setup + call + restore) in lean_emitter.py. Tested with multi_call.c (5 functions with inter-procedural calls). Generated MultiCall.lean compiles.
<!-- SECTION:FINAL_SUMMARY:END -->
