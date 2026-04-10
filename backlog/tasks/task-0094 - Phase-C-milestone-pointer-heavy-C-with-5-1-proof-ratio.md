---
id: TASK-0094
title: 'Phase C milestone: pointer-heavy C with <5:1 proof ratio'
status: To Do
assignee: []
created_date: '2026-04-10 05:18'
labels:
  - phase-c
  - milestone
  - test
dependencies:
  - TASK-0093
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
End-to-end test with pointer-heavy C code: linked list operations (insert, delete, reverse, length), or a small hash table, or a memory allocator (~300 LOC). Measure proof-to-code ratio. Target: <5:1 (vs seL4's 20:1). This validates that sep logic automation is working.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 300+ LOC pointer-heavy C module selected
- [ ] #2 All functions processed by CImporter + clift
- [ ] #3 At least 5 pointer-manipulating functions verified
- [ ] #4 Proof-to-code ratio measured: target <5:1
- [ ] #5 sep_auto handles 80%+ of sep logic obligations
- [ ] #6 No sorry in verified functions
<!-- AC:END -->
