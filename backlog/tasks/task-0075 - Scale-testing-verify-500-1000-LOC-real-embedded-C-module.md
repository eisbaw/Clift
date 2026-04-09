---
id: TASK-0075
title: 'Scale testing: verify 500-1000 LOC real embedded C module'
status: To Do
assignee: []
created_date: '2026-04-09 19:34'
labels:
  - phase-5
  - test
  - scaling
dependencies:
  - TASK-0049
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The current test suite covers small functions (5-20 LOC each). Need to test on a real embedded C module of 500-1000 LOC to identify scaling bottlenecks: CImporter limitations, proof term sizes, missing C features, tactic gaps. Candidates: a small crypto primitive (SHA-256 core), a CRC implementation, an embedded protocol parser, or a device driver.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Real C module (500+ LOC) selected and documented
- [ ] #2 CImporter processes the full module
- [ ] #3 At least 3 functions verified through the full pipeline
- [ ] #4 Scaling bottlenecks documented
- [ ] #5 Missing C features cataloged as backlog tasks
<!-- AC:END -->
