---
id: TASK-0133
title: 'Select industrial verification target: RTOS scheduler, crypto, or driver'
status: To Do
assignee: []
created_date: '2026-04-10 15:31'
labels:
  - phase-k
  - industrial
  - milestone
dependencies:
  - TASK-0116
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The ultimate validation: verify a real-world C component that people actually use. Candidates: (1) FreeRTOS scheduler core (~2000 LOC), (2) mbedTLS AES/SHA (~1500 LOC), (3) Zephyr UART driver (~800 LOC), (4) lwIP TCP/IP subset (~3000 LOC), (5) a custom embedded project. Selection criteria: open source, no floating point, well-structured, high assurance value, demonstrates Clift on code that matters.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Target selected with rationale
- [ ] #2 Feasibility assessment: which C features are used? Which does Clift support?
- [ ] #3 Verification plan: which functions first, what properties to prove
- [ ] #4 Effort estimate: person-weeks to complete
<!-- AC:END -->
