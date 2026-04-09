---
id: TASK-0073
title: Support function pointers and dispatch tables
status: To Do
assignee: []
created_date: '2026-04-09 19:34'
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
