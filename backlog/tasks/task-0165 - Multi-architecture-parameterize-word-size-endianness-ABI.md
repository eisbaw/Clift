---
id: TASK-0165
title: 'Multi-architecture: parameterize word size, endianness, ABI'
status: To Do
assignee: []
created_date: '2026-04-10 18:50'
labels:
  - phase-n
  - architecture
  - portability
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Our memory model hardcodes 32-bit address space (ADR-004) and little-endian byte encoding. seL4 supports ARM (32-bit LE), x86 (32/64-bit LE), RISC-V (32/64-bit LE). Need: (1) parameterize memSize by architecture (2^32 or 2^64), (2) parameterize byte encoding endianness, (3) parameterize struct layout by ABI (LP32, ILP32, LP64, LLP64), (4) CImporter takes --arch flag. This enables verifying code for multiple targets from the same source.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 memSize parameterized: 32-bit and 64-bit address spaces
- [ ] #2 Byte encoding parameterized: little-endian and big-endian
- [ ] #3 Struct layout parameterized by ABI (at least LP64 and ILP32)
- [ ] #4 CImporter --arch flag (arm32, arm64, x86, x86_64, riscv32, riscv64)
- [ ] #5 Same C source verified for two different architectures
- [ ] #6 Differential test: struct layout matches gcc for each arch
<!-- AC:END -->
