---
id: TASK-0011
title: 'Define HeapRawState, Ptr, ProcEnv, and CState'
status: Done
assignee:
  - '@mped'
created_date: '2026-04-08 21:35'
updated_date: '2026-04-08 22:54'
labels:
  - phase-0
  - csemantics
dependencies:
  - TASK-0007
references:
  - ext/AutoCorres2/c-parser/calculate_state.ML
  - ext/AutoCorres2/TypHeapSimple.thy
  - Clift/CSemantics/State.lean
  - Clift/CSemantics/ProcEnv.lean
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Define the state infrastructure: HeapRawState (flat byte memory + type descriptors), Ptr (typed pointer), ProcEnv (procedure name -> body map), and CState (globals + monolithic locals record). CState follows seL4's one-record-for-all-functions approach. Study calculate_state.ML for seL4's state generation.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 HeapRawState with mem (byte array) and htd (type descriptor) compiles
- [x] #2 Ptr structure with addr field compiles
- [x] #3 ProcEnv defined as map from ProcName to CSimpl bodies
- [x] #4 CState with globals and locals fields compiles
- [x] #5 TypeTag and basic CType typeclass skeleton defined
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
- HeapRawState, Ptr, ProcEnv, TypeTag already existed from tasks 0007/0010
- Added CType/MemType typeclass skeletons (size, align, typeTag, encode/decode)
- Added UInt32 CType instance
- Added Globals struct with rawHeap field
- Added CState parametric over Locals type
- Concrete test states (MaxState etc) will be defined per-test in task-0013
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Added CType/MemType typeclass skeletons, Globals structure, and CState parametric record to State.lean.
Existing HeapRawState, Ptr, ProcEnv, TypeTag were already in place from batch 2.
CState follows plan.md Decision 3 (one record for all functions).
All code compiles with lake build Clift.
<!-- SECTION:FINAL_SUMMARY:END -->
