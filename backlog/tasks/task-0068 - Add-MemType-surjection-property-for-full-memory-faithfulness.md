---
id: TASK-0068
title: Add MemType surjection property for full memory faithfulness
status: To Do
assignee: []
created_date: '2026-04-09 17:13'
labels:
  - phase-3c
  - future
dependencies: []
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Our MemType only has roundtrip : fromMem (toMem v) = v (injection). For full memory model correctness, we also need the surjection direction: for bytes in the image of toMem, toMem (fromMem bytes) = bytes. Without this, writing and reading back raw bytes might differ. This matters when reasoning about memory as bytes (e.g., memcpy). Low priority since TypHeapSimple also does not require this.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 MemType extended with surjection property
<!-- AC:END -->
