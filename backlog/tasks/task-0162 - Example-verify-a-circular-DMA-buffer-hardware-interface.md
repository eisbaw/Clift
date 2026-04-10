---
id: TASK-0162
title: 'Example: verify a circular DMA buffer (hardware interface)'
status: To Do
assignee: []
created_date: '2026-04-10 18:47'
labels:
  - phase-n
  - examples
  - embedded
  - hardware
dependencies: []
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
DMA buffers are critical in embedded systems — the hardware writes directly to memory. A circular DMA buffer (~200 LOC): init, get_write_ptr, advance_write, get_read_ptr, advance_read, bytes_available. Prove: read never overtakes write, write never overwrites unread data, hardware pointer advances correctly. Exercises: memory-mapped I/O, modular arithmetic, producer-consumer correctness.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 DMA buffer C source (200+ LOC)
- [ ] #2 Producer-consumer invariant: read <= write (modular)
- [ ] #3 No data loss: write never overwrites unread
- [ ] #4 No false reads: read never overtakes write
- [ ] #5 Hardware pointer model documented
<!-- AC:END -->
