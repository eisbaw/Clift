---
id: TASK-0167
title: 'Inline assembly boundary: axiomatize ASM and model C/ASM interface'
status: Done
assignee: []
created_date: '2026-04-10 18:50'
updated_date: '2026-04-10 23:22'
labels:
  - phase-n
  - asm
  - tcb
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
seL4 has ~340 lines of handwritten ARM assembly axiomatized as specs. Real embedded C uses inline asm for: interrupt enable/disable, memory barriers, cache flush, register access. Need: (1) syntax for declaring axiomatized ASM functions, (2) ASM functions get FuncSpecs with pre/post but no proof (trusted), (3) CImporter recognizes __asm__ blocks and emits axiomatized calls, (4) document: what's in the TCB (ASM specs) and what's proven (C code). Same trust model as seL4.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 AsmSpec type: FuncSpec without proof (axiomatized)
- [ ] #2 CImporter: __asm__ blocks emitted as CSimpl.call to axiomatized proc
- [ ] #3 Axiomatized procs clearly marked in generated code
- [ ] #4 TCB documentation updated: ASM specs are trusted
- [ ] #5 Example: disable_irq/enable_irq as axiomatized ASM
<!-- AC:END -->
