---
id: TASK-0088
title: 'CImporter: handle multi-function C files with calls'
status: To Do
assignee: []
created_date: '2026-04-10 05:17'
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
- [ ] #1 CImporter parses files with 5+ functions
- [ ] #2 Function calls emit CSimpl.call with correct ProcName
- [ ] #3 ProcEnv maps all function names to bodies
- [ ] #4 Return values from calls handled correctly
- [ ] #5 Pointer arguments to calls handled
- [ ] #6 Test: a C file with helper functions calling each other
<!-- AC:END -->
