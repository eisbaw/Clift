---
id: TASK-0016
title: 'CImporter: Python project setup and clang JSON schema'
status: To Do
assignee: []
created_date: '2026-04-08 21:35'
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
- [ ] #1 CImporter/import.py entry point exists with --help
- [ ] #2 pytest runs with at least one passing test
- [ ] #3 clang JSON schema for integer types, locals, if/else, while documented
- [ ] #4 test/clang_json/max.json generated and committed
- [ ] #5 just clang-dump works
<!-- AC:END -->
