---
id: TASK-0168
title: 'Compiler extensions: packed/aligned attributes, volatile, builtins'
status: To Do
assignee: []
created_date: '2026-04-10 18:50'
updated_date: '2026-04-14 22:12'
labels:
  - phase-g
  - cimporter
  - embedded
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Real embedded C uses: __attribute__((packed)) (no padding in structs), __attribute__((aligned(N))) (force alignment), volatile (MMIO, shared state), __builtin_clz/ctz/popcount (compiler intrinsics). Need: (1) packed structs: CImporter computes layout with zero padding, (2) aligned: force alignment in CType instance, (3) volatile: reads modeled as nondeterministic in CSimpl, (4) builtins: axiomatized with specs. These are essential for driver and firmware code.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 packed structs: CImporter respects __attribute__((packed))
- [ ] #2 aligned: CImporter respects __attribute__((aligned(N)))
- [ ] #3 volatile reads: modeled as nondeterministic (CSimpl.spec)
- [ ] #4 volatile writes: modeled as having external effect
- [ ] #5 __builtin_clz: axiomatized with correct spec
- [ ] #6 Test: MMIO register access via volatile pointer
<!-- AC:END -->
