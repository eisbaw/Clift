---
id: TASK-0179
title: 'Interrupt handling verification: delegation, acknowledgment, state consistency'
status: To Do
assignee: []
created_date: '2026-04-10 18:54'
labels:
  - phase-n
  - seL4-parity
  - kernel
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
TASK-0164 covers the concurrency/preemption execution model, but seL4 also verified specific interrupt handling properties: (1) interrupts are correctly acknowledged to hardware, (2) interrupts are correctly delegated to user-space handlers, (3) interrupt state (masked/unmasked, pending) is consistent, (4) interrupt handlers do not corrupt kernel state. Need: (1) Interrupt state model: pending, masked, handler mapping, (2) Interrupt delivery: from hardware -> kernel -> user handler, (3) Invariant: interrupt state consistent after every operation, (4) Example: verify an interrupt controller driver. This extends TASK-0164 (which covers the preemption model) with the functional correctness of interrupt management itself.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Interrupt state model defined
- [ ] #2 Interrupt delivery chain modeled
- [ ] #3 Interrupt state consistency invariant proven
- [ ] #4 Example: interrupt controller operations verified
<!-- AC:END -->
