---
id: TASK-0020
title: 'CImporter: end-to-end test with max.c and gcd.c'
status: To Do
assignee: []
created_date: '2026-04-08 21:35'
labels:
  - phase-1
  - cimporter
  - test
dependencies:
  - TASK-0019
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Run CImporter on test/c_sources/max.c and gcd.c. Verify generated .lean files compile. Create snapshot tests in test/expected/. Verify just import and just test-snapshots work.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 just import test/c_sources/max.c Max succeeds
- [ ] #2 just import test/c_sources/gcd.c Gcd succeeds
- [ ] #3 Generated/Max.lean compiles with lake build
- [ ] #4 Generated/Gcd.lean compiles with lake build
- [ ] #5 Snapshot tests created and just test-snapshots passes
<!-- AC:END -->
