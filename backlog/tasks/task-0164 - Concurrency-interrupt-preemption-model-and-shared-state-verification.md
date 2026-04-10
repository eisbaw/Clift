---
id: TASK-0164
title: 'Concurrency: interrupt preemption model and shared state verification'
status: To Do
assignee: []
created_date: '2026-04-10 18:50'
labels:
  - phase-n
  - concurrency
  - execution-model
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
seL4 proves correctness under interrupt preemption by showing the kernel runs with interrupts disabled at critical points. Real embedded C has ISRs that share state with main code. Need: (1) interrupt preemption points in the execution model, (2) volatile semantics (reads may return any value), (3) shared state model (ISR and main see same heap), (4) disable/enable interrupt primitives, (5) prove: critical sections are not preempted, shared state access is properly guarded. This is a major execution model extension.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Execution model extended with preemption points
- [ ] #2 Volatile reads modeled as nondeterministic
- [ ] #3 Interrupt disable/enable primitives in CSimpl
- [ ] #4 Shared state between main and ISR modeled
- [ ] #5 Example: ISR + main sharing a ring buffer with disable_irq guard
- [ ] #6 Critical section correctness proven
<!-- AC:END -->
