---
id: TASK-0255
title: Migrate hand-written L1 bodies to clift auto-generation
status: To Do
assignee: []
created_date: '2026-04-14 18:06'
labels:
  - credibility
  - infrastructure
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
12 files define L1 bodies manually instead of using clift auto-generation. These are valid (L1corres is proven) but fragile — if CImporter output changes, the hand-written body drifts.

Files to migrate:
- GcdProof.lean (SUPERSEDED by GcdEndToEnd.lean — move to cruft/)
- SwapProof.lean (l1_swap_body — needs clift Swap + re-prove validHoare)
- Rotate3Proof.lean (l1_rotate3_body, l1_abs_diff_body, l1_clamp_body)
- Sel4CapProof.lean (5 hand-written L1 bodies for cap operations)
- DmaBufferProof.lean (l1_dma_write_manual, l1_dma_read_manual — uses suffices bridge)

For each: run clift Module, prove validHoare against the auto-generated body, delete hand-written version.

GcdEndToEnd.lean demonstrates the pattern — use it as template.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 GcdProof.lean moved to cruft (superseded by GcdEndToEnd)
- [ ] #2 SwapProof.lean migrated to clift-generated L1
- [ ] #3 Rotate3Proof.lean migrated
- [ ] #4 Sel4CapProof.lean migrated
- [ ] #5 DmaBufferProof.lean migrated (remove manual bodies + suffices bridge)
- [ ] #6 Zero hand-written L1 bodies in just audit
<!-- AC:END -->
