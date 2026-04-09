---
id: TASK-0064
title: 'heapPtrValid: check ALL bytes in [addr, addr+size) have correct htd tag'
status: To Do
assignee: []
created_date: '2026-04-09 17:12'
labels:
  - phase-3c
  - soundness
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Currently heapPtrValid only checks the htd at the base address. Tuch's model and AutoCorres2 check that all bytes in the footprint have the right type tag. Without this, two overlapping typed regions could co-exist, leading to aliasing unsoundness. Need: for all i in [0, size), htd (addr + i) = some tag.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 heapPtrValid checks all bytes in footprint
- [ ] #2 hVal_heapUpdate_same still holds
- [ ] #3 hVal_heapUpdate_disjoint still holds
<!-- AC:END -->
