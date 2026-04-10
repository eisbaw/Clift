---
id: TASK-0151
title: 'Performance hardening: verify 100+ functions in <5 minutes'
status: To Do
assignee: []
created_date: '2026-04-10 18:46'
labels:
  - phase-o
  - performance
  - scalability
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
At seL4 scale (150 functions), the full build + proof check must be fast enough for CI. Target: 100+ functions verified in <5 minutes on a standard machine (4 cores, 16GB RAM). Profile the build, identify slow proofs, optimize or split them. Lake parallelism should help but may hit RAM limits.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 100+ function file created (expand ring_buffer_ext)
- [ ] #2 Full build + proof check time measured
- [ ] #3 Target: <5 minutes total
- [ ] #4 Slow proofs identified and optimized
- [ ] #5 RAM peak stays under 8GB
<!-- AC:END -->
