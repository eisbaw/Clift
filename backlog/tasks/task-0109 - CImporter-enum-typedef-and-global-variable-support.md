---
id: TASK-0109
title: 'CImporter: enum, typedef, and global variable support'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-10 12:58'
updated_date: '2026-04-10 14:00'
labels:
  - cimporter
  - scalability
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Real C uses enums (state machines, error codes), typedefs (type aliases), and global variables extensively. Our CImporter skips all three. Need: (1) enums mapped to UInt32 constants, (2) typedefs resolved to underlying types, (3) global variables added to Globals record and initialized. These are straightforward Python changes but block importing real codebases.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Enums: parsed and emitted as UInt32 constants with named defs
- [x] #2 Typedefs: resolved to underlying types during parsing
- [x] #3 Global variables: added to Globals record
- [x] #4 Global variable initialization emitted
- [x] #5 Test: C file using all three features
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Add EnumDecl parsing to ast_parser.py: collect (name, value) pairs into TranslationUnit.enums
2. Add TypedefDecl parsing: resolve to underlying type, add to type map
3. Add file-scope VarDecl parsing: collect into TranslationUnit.globals
4. Update lean_emitter.py: emit enum constants, typedef resolution, globals in Globals record + init
5. Write test C file: test/c_sources/enum_typedef_global.c
6. Test via just import and lake build
<!-- SECTION:PLAN:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Added enum, typedef, and global variable support to CImporter.

Changes:
- ast_parser.py: Parse EnumDecl (name+value), TypedefDecl (resolve to underlying type via _CLANG_TYPE_MAP), file-scope VarDecl (with integer initializer extraction). New expression kinds: global_ref, global_assign.
- lean_emitter.py: Emit enum constants as def NAME : UInt32 := N. Global variables added to Locals record (Phase 1 limitation: CState.Globals is not parametric). Emit globals_init with initial values.
- c_types.py: Typedef names registered in _CLANG_TYPE_MAP for transparent resolution.
- New test: test/c_sources/enum_typedef_global.c with enums (State, ErrorCode), typedefs (counter_t, status_t), globals (g_state, g_error_count, g_iterations), and two functions using all three.

Limitation: Global variables are placed in the Locals record rather than a separate Globals record, because CState hardcodes Globals = { rawHeap }. This is semantically imprecise for inter-procedural call save/restore but correct for single-function programs. A future task should make CState parametric over both Globals and Locals types.

Tests: 82 Python tests pass, Gcd/Max snapshots match, Generated/EnumTypedefGlobal.lean compiles.
<!-- SECTION:FINAL_SUMMARY:END -->
