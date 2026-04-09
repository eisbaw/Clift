---
id: TASK-0039
title: 'Differential test: struct sizes and offsets match gcc'
status: Done
assignee:
  - '@mped'
created_date: '2026-04-08 21:38'
updated_date: '2026-04-09 17:11'
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
- [x] #1 Test program that prints sizeof and offsetof for each test struct
- [x] #2 Python script compares gcc output against CImporter's generated CType instances
- [x] #3 Tested on: struct node, struct with padding, struct with alignment
- [x] #4 Any mismatch fails the test with clear error
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Differential test: struct sizes and offsets match gcc.
- test/c_sources/struct_sizes.c: 6 test structs covering no-padding, alignment-padding, self-referential pointers, mixed sizes, trailing padding, all-pointer
- test/test_struct_layout.py: compiles with gcc, runs binary, compares sizeof/offsetof/alignof against CImporter compute_struct_layout
- All 6 structs, all field offsets, sizes, and alignments match gcc exactly
- Added just test-struct-layout recipe, integrated into just e2e
<!-- SECTION:FINAL_SUMMARY:END -->
