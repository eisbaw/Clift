---
id: TASK-0122
title: 'CImporter: multi-file compilation units'
status: To Do
assignee: []
created_date: '2026-04-10 15:29'
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
- [ ] #1 Multiple .c files processed into separate .lean modules
- [ ] #2 Shared types emitted in common module
- [ ] #3 Extern declarations create cross-module ProcEnv references
- [ ] #4 Lake imports structured correctly
- [ ] #5 Test: 2-file C project with shared header
<!-- AC:END -->
