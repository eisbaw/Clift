---
id: TASK-0017
title: 'CImporter: parse clang JSON for integer types and local variables'
status: Done
assignee:
  - '@mped'
created_date: '2026-04-08 21:35'
updated_date: '2026-04-08 23:18'
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
- [x] #1 Parses function signature: name, return type, parameter names and types
- [x] #2 Parses local variable declarations with types
- [x] #3 Maps uint8/16/32/64_t and int8/16/32/64_t correctly
- [x] #4 Rejects unsupported C features (float, goto, address-of locals) with clear error
- [x] #5 Unit tests for each parser feature pass
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
All parser features implemented in ast_parser.py:
- Function signatures parsed from FunctionDecl nodes
- Local vars collected recursively from VarDecl nodes
- All integer type mappings in c_types.py
- StrictC violations raise clear StrictCViolation exceptions
- 18 parser-specific tests pass
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Clang JSON AST parsing implemented in ast_parser.py with c_types.py type mapping.

Key decisions:
- Use desugaredQualType from clang (canonical form) over qualType
- StrictCViolation exception for rejected constructs
- Intermediate representation: VarInfo, Expr, Stmt, FuncInfo dataclasses
- Ternary operators parsed as expressions (not control flow)
<!-- SECTION:FINAL_SUMMARY:END -->
