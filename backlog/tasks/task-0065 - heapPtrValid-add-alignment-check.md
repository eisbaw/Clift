---
id: TASK-0065
title: 'heapPtrValid: add alignment check'
status: To Do
assignee: []
created_date: '2026-04-09 17:13'
labels:
  - phase-3c
  - soundness
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Tuch's c_guard and AutoCorres2 root_ptr_valid require that pointers are aligned to the type's natural alignment. Our heapPtrValid checks non-null and in-bounds but does NOT check alignment. On x86-64, unaligned access works but is UB per the C standard. We should add: p.addr.val % CType.align = 0.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 heapPtrValid checks addr % align = 0
- [ ] #2 All existing proofs still hold
<!-- AC:END -->
