---
id: TASK-0201
title: Eliminate 2 sorry in UartDriverProof.lean
status: To Do
assignee: []
created_date: '2026-04-10 20:50'
labels:
  - sorry-elimination
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
2 sorry: one requires heap write reasoning for 11 field assignments, one requires heap read + field projection.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 All 2 sorry eliminated
- [ ] #2 All proofs kernel-checked
<!-- AC:END -->
