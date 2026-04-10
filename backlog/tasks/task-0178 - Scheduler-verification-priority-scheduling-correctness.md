---
id: TASK-0178
title: 'Scheduler verification: priority scheduling correctness'
status: To Do
assignee: []
created_date: '2026-04-10 18:53'
labels:
  - phase-n
  - seL4-parity
  - kernel
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
seL4 verified its round-robin + priority scheduler: highest-priority runnable thread always runs, time-slice accounting is correct, priority inversion is bounded. Need: (1) Scheduler abstract model (ready queues per priority, time-slice counter), (2) Scheduling invariant: highest-priority runnable thread is selected, (3) Operations: enqueue, dequeue, yield, priority change, (4) Verify a concrete C scheduler implementation, (5) Prove: no priority inversion without proper protocol. This exercises array/list manipulation, integer arithmetic, and the concurrency model (scheduler runs with interrupts disabled).
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Scheduler abstract model with priority queues
- [ ] #2 Scheduling invariant defined
- [ ] #3 At least 3 operations verified
- [ ] #4 Example: simple priority scheduler in C verified
<!-- AC:END -->
