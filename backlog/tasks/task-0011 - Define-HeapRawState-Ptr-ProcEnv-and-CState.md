---
id: TASK-0011
title: 'Define HeapRawState, Ptr, ProcEnv, and CState'
status: To Do
assignee: []
created_date: '2026-04-08 21:35'
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
- [ ] #1 HeapRawState with mem (byte array) and htd (type descriptor) compiles
- [ ] #2 Ptr structure with addr field compiles
- [ ] #3 ProcEnv defined as map from ProcName to CSimpl bodies
- [ ] #4 CState with globals and locals fields compiles
- [ ] #5 TypeTag and basic CType typeclass skeleton defined
<!-- AC:END -->
