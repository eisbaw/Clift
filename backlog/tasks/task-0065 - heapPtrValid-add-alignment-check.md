---
id: TASK-0065
title: 'heapPtrValid: add alignment check'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-09 17:13'
updated_date: '2026-04-09 20:10'
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
- [x] #1 heapPtrValid checks addr % align = 0
- [x] #2 All existing proofs still hold
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Added alignment check to heapPtrValid: addr % align = 0. This prevents misaligned memory access (UB in C). The alignment requirement is part of the CType typeclass so each type specifies its natural alignment (UInt32=4, UInt64=8, Ptr=8, etc.). All existing proofs pass since alignment is a pure address property preserved by heap writes.
<!-- SECTION:FINAL_SUMMARY:END -->
