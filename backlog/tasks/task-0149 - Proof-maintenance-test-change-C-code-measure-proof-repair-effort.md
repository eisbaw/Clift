---
id: TASK-0149
title: 'Proof maintenance test: change C code, measure proof repair effort'
status: To Do
assignee: []
created_date: '2026-04-10 18:46'
labels:
  - phase-o
  - maintenance
  - hardening
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
seL4's proofs have been maintained for 15 years. When the C changes, how much proof breaks? Test: (1) add a field to ring_buffer struct, (2) change an algorithm (e.g., linear search to binary search in contains), (3) add a new function. For each change: measure how many proofs break, how long to fix, which proofs are fragile vs robust. This validates our proof architecture is maintainable.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Test 1: add struct field — measure broken proofs and fix time
- [ ] #2 Test 2: change algorithm — measure broken proofs and fix time
- [ ] #3 Test 3: add new function — measure effort to verify it
- [ ] #4 Fragile vs robust proofs identified
- [ ] #5 Recommendations for proof architecture improvements
<!-- AC:END -->
