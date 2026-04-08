---
id: TASK-0018
title: 'CImporter: emit Globals, Locals, CState Lean structures'
status: To Do
assignee: []
created_date: '2026-04-08 21:35'
labels:
  - phase-1
  - cimporter
dependencies:
  - TASK-0017
references:
  - ext/AutoCorres2/c-parser/calculate_state.ML
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Implement lean_emitter.py: generate the Lean 4 state record structures. Globals (with rawHeap field), Locals (merged from all functions — same-name same-type locals share a field, different-type get qualified names), CState (globals + locals). Output must be valid Lean 4 that compiles when imported alongside Clift.CSemantics.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Emits structure Globals with rawHeap field
- [ ] #2 Emits structure Locals merging all functions' locals
- [ ] #3 Same-name, same-type locals share one field
- [ ] #4 Same-name, different-type locals get type-qualified names (e.g. x_unsigned)
- [ ] #5 Emits structure CState with globals and locals fields
- [ ] #6 Generated .lean compiles with import Clift.CSemantics
<!-- AC:END -->
