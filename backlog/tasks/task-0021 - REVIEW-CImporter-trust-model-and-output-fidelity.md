---
id: TASK-0021
title: 'REVIEW: CImporter trust model and output fidelity'
status: To Do
assignee: []
created_date: '2026-04-08 21:36'
labels:
  - review
  - phase-1
  - cimporter
dependencies:
  - TASK-0020
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
MPED review of CImporter (tasks 0016-0020). Critical: the importer is in the TCB. Review: does generated CSimpl faithfully represent the C source? Test C semantics edge cases: integer promotion, unsigned wrapping, implicit conversions. Diff importer output against what AutoCorres2's C parser produces for the same input (manual comparison).
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Generated CSimpl for max.c manually verified against C semantics
- [ ] #2 Generated CSimpl for gcd.c manually verified against C semantics
- [ ] #3 Integer promotion edge cases tested (e.g. uint8 + uint8 promotes to int)
- [ ] #4 Unsigned wrapping behavior correctly represented
- [ ] #5 Output compared against ext/AutoCorres2/c-parser output patterns
- [ ] #6 Trust model documented: what can go wrong, what mitigations exist
<!-- AC:END -->
