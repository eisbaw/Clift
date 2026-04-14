---
id: TASK-0141
title: 'CImporter: integer promotion and implicit conversion audit'
status: To Do
assignee: []
created_date: '2026-04-10 18:46'
updated_date: '2026-04-14 22:12'
labels:
  - phase-m
  - testing
  - tcb
  - hardening
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
C's integer promotion rules are notoriously subtle. uint8 + uint8 promotes to int (signed!). char might be signed or unsigned. Arithmetic between different-width types has implicit conversions. Audit every arithmetic operation in the CImporter for correct promotion. Compare against C11 standard Section 6.3.1.1 (Integer promotions) and 6.3.1.8 (Usual arithmetic conversions). This is in the TCB — getting promotions wrong invalidates all proofs.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Every arithmetic BinaryOperator in lean_emitter.py audited for promotion
- [ ] #2 Test: uint8_t a = 200; uint8_t b = 200; uint32_t c = a + b; (should be 400, not 144)
- [ ] #3 Test: int8_t + uint8_t (signed + unsigned promotion)
- [ ] #4 Test: uint16_t * uint16_t (promotes to int, may overflow signed)
- [ ] #5 All promotion bugs fixed
- [ ] #6 Regression tests for each edge case
<!-- AC:END -->
