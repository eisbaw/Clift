---
id: TASK-0110
title: 'Scalability: measure and optimize build time at 50+ function scale'
status: To Do
assignee: []
created_date: '2026-04-10 12:58'
labels:
  - scalability
  - performance
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
At seL4 scale (150 functions), build time matters. Currently untested beyond 16 functions. Need: (1) measure lake build time as function count grows (20, 50, 100 functions), (2) identify bottlenecks (type-checking? elaboration? import resolution?), (3) optimize: split Generated/ into multiple files? parallelize? use opaque defs? (4) incremental builds: does changing one function's proof re-check only dependents? Lake should handle this, but verify.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Build time measured at 20, 50, 100 generated functions
- [ ] #2 Bottleneck identified (type-checking vs elaboration vs import)
- [ ] #3 Strategy for sub-linear build time documented
- [ ] #4 Incremental build tested: change one proof, verify only dependents rebuild
<!-- AC:END -->
