---
id: TASK-0199
title: Eliminate 2 sorry in Sha256CoreProof.lean
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
2 sorry: one requires unfolding L1 bitwise ops with UInt32 bitwise lemmas, one requires heap write reasoning for 9 field assignments. May be blocked on CImporter bitwise support (task 0119).
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 All 2 sorry eliminated
- [ ] #2 All proofs kernel-checked
<!-- AC:END -->
