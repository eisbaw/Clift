---
id: TASK-0097
title: Select and import 1000+ LOC embedded C module for verification
status: To Do
assignee: []
created_date: '2026-04-10 05:19'
labels:
  - phase-d
  - test
  - scaling
dependencies:
  - TASK-0084
  - TASK-0089
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Find a real embedded C module of 1000+ LOC suitable for verification. Candidates: (1) a crypto primitive like SHA-256 or AES, (2) a protocol parser (MQTT, CoAP), (3) a device driver for a simple peripheral (UART, SPI, I2C), (4) a memory allocator (dlmalloc subset), (5) an RTOS scheduler core. Selection criteria: no floating point, no dynamic allocation (or minimal), mostly sequential, uses structs and pointers, real-world relevance. Import with CImporter, run clift, identify gaps.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Module selected with rationale documented
- [ ] #2 CImporter processes all files (may need CImporter fixes — file as subtasks)
- [ ] #3 clift lifts all functions
- [ ] #4 Gap analysis: which C features are missing?
- [ ] #5 Verification plan: which functions to verify first, what specs to write
<!-- AC:END -->
