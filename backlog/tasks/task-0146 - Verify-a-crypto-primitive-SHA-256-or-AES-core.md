---
id: TASK-0146
title: 'Verify a crypto primitive: SHA-256 or AES core'
status: To Do
assignee: []
created_date: '2026-04-10 18:46'
updated_date: '2026-04-14 22:12'
labels:
  - phase-n
  - industrial
  - crypto
  - real-world
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Crypto code is THE highest-assurance target. mbedTLS SHA-256 (~500 LOC) or a standalone implementation. Crypto verification exercises: bitwise ops, array manipulation, loop-heavy computation, exact bit-level correctness. The spec is the algorithm itself (FIPS 180-4 for SHA-256). Prove: output matches the mathematical definition for all inputs.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 SHA-256 or AES C source imported
- [ ] #2 All functions lifted with clift
- [ ] #3 Mathematical spec: SHA-256 as a Lean function over ByteArray
- [ ] #4 At least the compression function verified against spec
- [ ] #5 Constant-time property stated (no data-dependent branches)
- [ ] #6 No sorry in verified functions
<!-- AC:END -->
