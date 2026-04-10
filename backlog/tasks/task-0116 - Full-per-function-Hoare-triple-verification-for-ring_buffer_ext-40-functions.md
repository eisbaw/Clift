---
id: TASK-0116
title: Full per-function Hoare triple verification for ring_buffer_ext (40 functions)
status: To Do
assignee: []
created_date: '2026-04-10 15:29'
labels:
  - phase-f
  - verification
  - milestone
dependencies:
  - TASK-0115
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Prove validHoare (pre/post) for ALL 40 functions in ring_buffer_ext.c. Use the Claude proof engine (task-0115) + MetaM VCG + manual intervention where needed. Each function gets a FuncSpec. This is the seL4-equivalent deliverable: every function proven correct against its spec, not just abstract properties. Measure: how many functions can Claude prove fully automatically? How many need human help?
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 FuncSpec defined for all 40 functions
- [ ] #2 validHoare proven for at least 35/40 functions
- [ ] #3 Remaining 5 documented with what's blocking them
- [ ] #4 Proof-to-code ratio measured
- [ ] #5 Claude automation rate measured (fully auto / needs hints / manual)
- [ ] #6 No sorry in final verified functions
<!-- AC:END -->
