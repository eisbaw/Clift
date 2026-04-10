---
id: TASK-0183
title: 'CImporter validation against C11 standard: comprehensive semantics coverage'
status: Done
assignee: []
created_date: '2026-04-10 18:54'
updated_date: '2026-04-10 19:53'
labels:
  - phase-m
  - soundness
  - tcb
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
TASK-0141 covers integer promotion audit, but the C standard has many more semantic subtleties that the CImporter must handle correctly: (1) Sequence points and evaluation order (C11 6.5), (2) Pointer aliasing and strict aliasing rules (C11 6.5p7), (3) Object lifetime and effective type (C11 6.5p6), (4) Undefined behavior catalog: systematically check each UB from Annex J against CImporter handling, (5) Implementation-defined behavior: document what Clift assumes (two's complement, etc.), (6) Volatile semantics (C11 6.7.3p7). The CImporter is in the TCB -- any mistranslation silently invalidates all proofs. This is broader than TASK-0141 (integers only) and TASK-0143 (memory model only).
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Evaluation order: CImporter enforces no side effects in expressions (StrictC)
- [ ] #2 Strict aliasing: documented treatment in memory model
- [ ] #3 UB catalog: each Annex J item classified as handled/excluded/not-applicable
- [ ] #4 Implementation-defined: all assumptions documented
- [ ] #5 Volatile: treatment documented (excluded from StrictC or modeled)
<!-- AC:END -->
