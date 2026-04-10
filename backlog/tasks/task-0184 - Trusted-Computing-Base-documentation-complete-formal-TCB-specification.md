---
id: TASK-0184
title: 'Trusted Computing Base documentation: complete formal TCB specification'
status: To Do
assignee: []
created_date: '2026-04-10 18:54'
labels:
  - phase-l
  - industrial
  - documentation
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
seL4 explicitly documents every assumption in the TCB: hardware correctness, assembly code, compiler, boot loader, etc. Clift needs the same. Need: (1) Complete list of trusted components: Lean 4 kernel, CImporter, clang -ast-dump, Lean/Mathlib axioms (propext, choice, Quot.sound), (2) Complete list of assumptions: target ABI matches model, no hardware faults, no memory corruption outside model, (3) Complete list of EXCLUDED C features and WHY, (4) Clear statement: what is proven vs what is assumed, (5) Formal threat model: what attacks are prevented by Clift proofs. This document is essential for industrial adoption and certification (DO-178C, CC EAL). A single page that a formal methods expert can review to understand the assurance argument.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 TCB components listed with justification
- [ ] #2 All assumptions listed explicitly
- [ ] #3 Excluded C features documented
- [ ] #4 Proven-vs-assumed boundary clear
- [ ] #5 Threat model documented
<!-- AC:END -->
