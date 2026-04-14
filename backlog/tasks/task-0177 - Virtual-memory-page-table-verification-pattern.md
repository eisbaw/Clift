---
id: TASK-0177
title: Virtual memory / page table verification pattern
status: Done
assignee: []
created_date: '2026-04-10 18:53'
updated_date: '2026-04-10 23:39'
labels:
  - phase-n
  - seL4-parity
  - kernel
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
seL4 verified page table management: virtual-to-physical address translation, TLB consistency, and that page table operations maintain the mapping invariant. Any OS kernel verification needs this. Need: (1) Page table abstract model (multi-level page table as a Lean structure), (2) Page table operations: map, unmap, lookup, (3) Invariant: page table entries are consistent with the mapping, (4) CImporter support for the C patterns used in page table code (bitwise ops on PTEs, array indexing into page tables), (5) Example: verify a simple 2-level page table map/unmap. This is a data structure verification problem that exercises bitwise ops, pointer arithmetic, and array access heavily.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Page table abstract model defined
- [ ] #2 Map/unmap/lookup operations specified
- [ ] #3 Page table invariant defined and preserved by operations
- [ ] #4 Example: 2-level page table verified
<!-- AC:END -->
