---
id: TASK-0133
title: 'Select industrial verification target: RTOS scheduler, crypto, or driver'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-10 15:31'
updated_date: '2026-04-10 18:35'
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
- [x] #1 Target selected with rationale
- [x] #2 Feasibility assessment: which C features are used? Which does Clift support?
- [x] #3 Verification plan: which functions first, what properties to prove
- [x] #4 Effort estimate: person-weeks to complete
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Selected ring_buffer_ext.c (676 LOC, 40 functions) as industrial target. Feasibility assessment in docs/industrial-target.md evaluates 5 candidates. FreeRTOS/mbedTLS blocked by inline asm and type punning. ring_buffer_ext exercises all supported C features and is already fully imported.
<!-- SECTION:FINAL_SUMMARY:END -->
