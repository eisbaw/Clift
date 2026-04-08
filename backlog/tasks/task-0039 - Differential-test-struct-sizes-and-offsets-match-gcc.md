---
id: TASK-0039
title: 'Differential test: struct sizes and offsets match gcc'
status: To Do
assignee: []
created_date: '2026-04-08 21:38'
labels:
  - phase-3b
  - test
  - risk-mitigation
dependencies:
  - TASK-0038
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Write test infrastructure that compiles C structs with gcc, extracts sizeof/offsetof via a test program, and compares against our CType instances. This catches silent ABI mismatches that would invalidate all struct-related proofs. Risk mitigation for Risk #7.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Test program that prints sizeof and offsetof for each test struct
- [ ] #2 Python script compares gcc output against CImporter's generated CType instances
- [ ] #3 Tested on: struct node, struct with padding, struct with alignment
- [ ] #4 Any mismatch fails the test with clear error
<!-- AC:END -->
