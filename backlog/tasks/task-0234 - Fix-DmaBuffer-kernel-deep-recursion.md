---
id: TASK-0234
title: Fix DmaBuffer kernel deep recursion
status: Done
assignee: []
created_date: '2026-04-12 12:22'
updated_date: '2026-04-12 22:40'
labels:
  - kernel-depth
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
dma_write_correct and dma_read_correct hit kernel deep recursion on 11-field Locals. Convert step functions to anonymous constructors.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 All step functions use anonymous constructors
- [ ] #2 lake build Examples.DmaBufferProof succeeds
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
DmaBuffer kernel depth fixed. dma_write and dma_read build clean with 0 sorry.
<!-- SECTION:FINAL_SUMMARY:END -->
