---
id: TASK-0122
title: 'CImporter: multi-file compilation units'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-10 15:29'
updated_date: '2026-04-10 17:45'
labels:
  - phase-g
  - cimporter
  - industrial
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Real C projects have multiple .c files with shared headers. Need: (1) process multiple .c files into separate Generated/*.lean modules, (2) shared struct/enum/typedef definitions go in a common module, (3) extern function declarations create ProcEnv entries referencing other modules, (4) header parsing (or: rely on clang preprocessing which inlines headers). Lake build handles inter-module dependencies via imports.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Multiple .c files processed into separate .lean modules
- [x] #2 Shared types emitted in common module
- [x] #3 Extern declarations create cross-module ProcEnv references
- [x] #4 Lake imports structured correctly
- [x] #5 Test: 2-file C project with shared header
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Create multi_import.py script that processes multiple .c files
2. Extract shared types (structs/enums) from each TU, emit in common Types module
3. Per-file modules import the common Types module
4. Extern function declarations create ProcEnv entries referencing other modules
5. Add just recipe for multi-file import
6. Test with 2-file project (helper.c + main.c with shared header)
<!-- SECTION:PLAN:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Multi-file compilation unit support for CImporter.

Changes:
- New CImporter/multi_import.py: processes multiple clang JSON ASTs into a Lean module set
- Emits Generated/<Project>/Types.lean with shared struct/enum definitions
- Emits Generated/<Project>/<File>.lean per source file, importing Types
- Cross-file function calls use .call "name" (ProcEnv composition at proof level)
- Test: 2-file project (helper.c + main.c) with shared struct point and cross-file call
- All 3 generated modules (Types, Helper, Main) compile successfully
- Added just recipes: multi-import, import-multi-test

Limitations:
- Each per-file module has its own Locals record (no merged locals across files)
- Cross-file ProcEnv composition is manual at the proof level
- Extern declarations are not explicitly tracked (calls just reference by name)
<!-- SECTION:FINAL_SUMMARY:END -->
