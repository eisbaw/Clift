---
id: TASK-0145
title: Verify FreeRTOS queue.c or equivalent RTOS primitive
status: Done
assignee: []
created_date: '2026-04-10 18:46'
updated_date: '2026-04-10 20:13'
labels:
  - phase-n
  - industrial
  - real-world
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Verify a real RTOS queue implementation — the kind of code that runs in medical devices, automotive ECUs, and industrial controllers. FreeRTOS queue.c (~600 LOC) is the canonical target. If FreeRTOS is too complex (uses macros, portability layers), use Zephyr's k_queue or write a faithful reimplementation. Full pipeline: import, lift, spec, verify, security properties.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 RTOS queue C source imported (600+ LOC)
- [ ] #2 All functions lifted with clift
- [ ] #3 Abstract spec: bounded blocking queue with priority
- [ ] #4 At least 10 functions fully verified (validHoare + totalHoare)
- [ ] #5 Thread safety property stated (even if not fully proven for concurrent access)
- [ ] #6 No sorry in verified functions
<!-- AC:END -->
