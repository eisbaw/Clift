---
id: TASK-0166
title: >-
  Regression suite: comprehensive test infrastructure for continuous
  verification
status: To Do
assignee: []
created_date: '2026-04-10 18:50'
labels:
  - phase-o
  - testing
  - infrastructure
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
seL4 re-verifies on every commit. We need: (1) a regression suite that covers every CImporter feature (one .c file per feature), (2) regression for every lifting stage (L1 through L5 on representative functions), (3) regression for every proof (key theorems re-checked), (4) performance regression (build time and RAM tracked over time), (5) CImporter output stability (snapshot tests for all Generated/ files). This becomes the safety net that catches regressions as the tool evolves.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 CImporter feature regression: one .c per feature (30+ test files)
- [ ] #2 Lifting regression: representative functions through each stage
- [ ] #3 Proof regression: key theorems listed and checked
- [ ] #4 Performance regression: build time and RAM tracked
- [ ] #5 Snapshot stability: all Generated/ files have expected/ counterparts
- [ ] #6 just regression runs full suite in <10 minutes
<!-- AC:END -->
