---
id: TASK-0147
title: 'Verify a device driver: UART or SPI register manipulation'
status: To Do
assignee: []
created_date: '2026-04-10 18:46'
updated_date: '2026-04-14 22:12'
labels:
  - phase-n
  - industrial
  - drivers
  - real-world
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Driver code exercises bitwise ops, memory-mapped I/O, register manipulation, state machines. Write or find a 300-400 LOC UART driver (init, send, receive, interrupt handler). Model MMIO registers as heap locations with specific addresses. Prove: init sets registers correctly, send/receive follow protocol, interrupt handler preserves driver state invariant.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 UART driver C source (300+ LOC)
- [ ] #2 MMIO registers modeled as heap locations
- [ ] #3 Driver state machine spec defined
- [ ] #4 init verified: registers set to correct values
- [ ] #5 send/receive verified: data transferred correctly
- [ ] #6 State machine invariant preserved
<!-- AC:END -->
