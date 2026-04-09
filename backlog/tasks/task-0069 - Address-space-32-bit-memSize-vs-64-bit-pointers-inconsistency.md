---
id: TASK-0069
title: 'Address space: 32-bit memSize vs 64-bit pointers inconsistency'
status: To Do
assignee: []
created_date: '2026-04-09 17:13'
labels:
  - phase-3c
  - review
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
memSize is 2^32 (32-bit address space) but Ptr stores addresses as UInt64 (8 bytes). On LP64, addresses are 64-bit. Either memSize should be 2^48 (or 2^64) for LP64, or Ptr should store 4-byte addresses. Currently Ptr.fromBytes uses mod memSize to truncate, which silently loses high bits. This is technically sound (addresses that don't fit wrap) but could mask bugs. Filed as a consistency review item.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Document or fix the 32-bit/64-bit inconsistency
<!-- AC:END -->
