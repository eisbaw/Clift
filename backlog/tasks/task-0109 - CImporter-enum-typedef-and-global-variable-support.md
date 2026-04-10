---
id: TASK-0109
title: 'CImporter: enum, typedef, and global variable support'
status: To Do
assignee: []
created_date: '2026-04-10 12:58'
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
- [ ] #1 Enums: parsed and emitted as UInt32 constants with named defs
- [ ] #2 Typedefs: resolved to underlying types during parsing
- [ ] #3 Global variables: added to Globals record
- [ ] #4 Global variable initialization emitted
- [ ] #5 Test: C file using all three features
<!-- AC:END -->
