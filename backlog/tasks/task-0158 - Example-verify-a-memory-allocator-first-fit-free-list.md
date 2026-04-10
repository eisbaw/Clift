---
id: TASK-0158
title: 'Example: verify a memory allocator (first-fit, free list)'
status: To Do
assignee: []
created_date: '2026-04-10 18:47'
labels:
  - phase-n
  - examples
  - allocator
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Memory allocators are critical for safety — use-after-free, double-free, buffer overflow all originate here. Write a simple first-fit allocator (~400 LOC): init, malloc, free, realloc. Prove: allocated blocks don't overlap, freed blocks return to free list, no use-after-free possible, total allocated <= pool size. This is one of the hardest verification targets — seL4 axiomatized their allocator.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Allocator C source (400+ LOC)
- [ ] #2 Free list invariant defined and proven
- [ ] #3 malloc returns non-overlapping blocks
- [ ] #4 free returns block to free list
- [ ] #5 Total allocation bounded by pool size
- [ ] #6 No sorry
<!-- AC:END -->
