---
id: TASK-0018
title: 'CImporter: emit Globals, Locals, CState Lean structures'
status: Done
assignee:
  - '@mped'
created_date: '2026-04-08 21:35'
updated_date: '2026-04-08 23:18'
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
- [x] #1 Emits structure Globals with rawHeap field
- [x] #2 Emits structure Locals merging all functions' locals
- [x] #3 Same-name, same-type locals share one field
- [x] #4 Same-name, different-type locals get type-qualified names (e.g. x_unsigned)
- [x] #5 Emits structure CState with globals and locals fields
- [x] #6 Generated .lean compiles with import Clift.CSemantics
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
State structures implemented in lean_emitter.py:
- Reuses library Globals (has rawHeap) rather than redefining
- Emits per-program Locals structure with merged fields
- abbrev ProgramState := CState Locals uses library generic CState
- Namespace per module avoids name conflicts
- Type qualification for same-name different-type vars implemented
- Both Max.lean and Gcd.lean compile successfully
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Lean state structure emission implemented.

Design: reuse library Globals + CState, generate only Locals per program.
abbrev ProgramState := CState Locals provides the full state type.
Namespaced to avoid conflicts between generated modules.
<!-- SECTION:FINAL_SUMMARY:END -->
