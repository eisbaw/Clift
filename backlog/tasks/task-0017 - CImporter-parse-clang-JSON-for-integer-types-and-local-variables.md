---
id: TASK-0017
title: 'CImporter: parse clang JSON for integer types and local variables'
status: To Do
assignee: []
created_date: '2026-04-08 21:35'
labels:
  - phase-1
  - cimporter
dependencies:
  - TASK-0016
references:
  - ext/AutoCorres2/c-parser/calculate_state.ML
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Implement ast_parser.py: traverse clang JSON AST, extract function declarations, parameter types, local variable declarations, and their C types. Map C integer types (uint8_t through int64_t) to internal representations. Handle the StrictC restrictions (reject unsupported constructs with clear errors).
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Parses function signature: name, return type, parameter names and types
- [ ] #2 Parses local variable declarations with types
- [ ] #3 Maps uint8/16/32/64_t and int8/16/32/64_t correctly
- [ ] #4 Rejects unsupported C features (float, goto, address-of locals) with clear error
- [ ] #5 Unit tests for each parser feature pass
<!-- AC:END -->
