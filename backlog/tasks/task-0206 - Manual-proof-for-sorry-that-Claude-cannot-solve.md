---
id: TASK-0206
title: Manual proof for sorry that Claude cannot solve
status: To Do
assignee: []
created_date: '2026-04-11 06:28'
labels:
  - sorry-elimination
  - proof-depth
dependencies:
  - TASK-0205
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
After the batch sorry elimination (task-0205), ~12 sorry will likely remain. These are the hard ones: complex loop invariants, deep heap reasoning, mutual induction. For each: analyze why Claude failed, write the proof manually or with heavy human guidance. Document each as a case study for improving the proof engine.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Each remaining sorry analyzed: root cause documented
- [ ] #2 At least 8 of remaining sorry eliminated manually
- [ ] #3 Case studies written: what made each proof hard for Claude
- [ ] #4 Proof engine improvement suggestions filed as tasks
<!-- AC:END -->
