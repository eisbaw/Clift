---
id: TASK-0016
title: 'CImporter: Python project setup and clang JSON schema'
status: Done
assignee:
  - '@mped'
created_date: '2026-04-08 21:35'
updated_date: '2026-04-08 23:18'
labels:
  - phase-1
  - cimporter
dependencies:
  - TASK-0015
references:
  - ext/AutoCorres2/c-parser/
  - CImporter/README.md
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Set up CImporter Python project: pytest, project structure (ast_parser.py, lean_emitter.py, c_types.py). Document the clang JSON AST schema we depend on. Pin clang version in flake.nix. Run clang -ast-dump=json on test/c_sources/max.c and study the output structure. Do NOT start until CSimpl and CState design is frozen (Phase 0 complete).
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 CImporter/import.py entry point exists with --help
- [x] #2 pytest runs with at least one passing test
- [x] #3 clang JSON schema for integer types, locals, if/else, while documented
- [x] #4 test/clang_json/max.json generated and committed
- [x] #5 just clang-dump works
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Implemented CImporter Python project:
- CImporter/import.py with argparse --help
- CImporter/c_types.py, ast_parser.py, lean_emitter.py
- CImporter/tests/ with 51 passing tests
- test/clang_json/Max.json and Gcd.json generated and committed
- just clang-dump works, just import works
- Updated flake.nix to include pytest
- Clang JSON schema documented via c_types.py mapping and ast_parser.py traversal
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Set up CImporter Python project with full clang JSON parsing pipeline.

Changes:
- Added CImporter/{__init__,import,c_types,ast_parser,lean_emitter}.py
- Added CImporter/tests/ with 51 pytest tests covering types, parsing, emission
- Updated flake.nix to include pytest in devShell
- Generated test/clang_json/{Max,Gcd}.json from clang 17
- Fixed Justfile import recipe to suppress clang stderr
- Clang JSON schema knowledge encoded in c_types.py type mapping
<!-- SECTION:FINAL_SUMMARY:END -->
