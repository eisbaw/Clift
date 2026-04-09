---
id: TASK-0064
title: 'heapPtrValid: check ALL bytes in [addr, addr+size) have correct htd tag'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-09 17:12'
updated_date: '2026-04-09 20:10'
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
- [x] #1 heapPtrValid checks all bytes in footprint
- [x] #2 hVal_heapUpdate_same still holds
- [x] #3 hVal_heapUpdate_disjoint still holds
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Strengthened heapPtrValid to check ALL bytes in [addr, addr+size) have the correct type tag. Previously only checked the base address. The htd check now uses a universal quantifier over the byte range with modular arithmetic for Fin construction. All downstream proofs (heapUpdate_preserves_heapPtrValid, simpleLift lemmas, sep logic) continue to hold since they go through the heapPtrValid_bound and heapUpdate_htd helper theorems.
<!-- SECTION:FINAL_SUMMARY:END -->
