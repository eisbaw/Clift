---
id: TASK-0124
title: 'CImporter: string literals and char arrays'
status: To Do
assignee: []
created_date: '2026-04-10 15:29'
labels:
  - phase-g
  - cimporter
dependencies: []
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
C strings are const char arrays. Need: (1) string literals emitted as heap-allocated byte arrays, (2) char* type supported (Ptr UInt8), (3) basic string operations (strlen, strcmp) can be modeled. Not essential for kernel/driver verification but needed for protocol parsers and user-facing code.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 String literals parsed and emitted as initialized byte arrays
- [ ] #2 char/char* types mapped to UInt8/Ptr UInt8
- [ ] #3 Test: C function that checks string equality
<!-- AC:END -->
