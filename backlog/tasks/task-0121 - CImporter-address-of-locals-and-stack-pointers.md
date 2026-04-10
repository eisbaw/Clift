---
id: TASK-0121
title: 'CImporter: address-of locals and stack pointers'
status: To Do
assignee: []
created_date: '2026-04-10 15:29'
labels:
  - phase-g
  - cimporter
  - memory-model
dependencies: []
references:
  - ext/AutoCorres2/Stack_Typing.thy
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
seL4's StrictC forbids address-of locals, but real embedded C does &local_var constantly (passing local arrays to functions, out-parameters). Need: (1) model local variables as heap-allocated (or stack-modeled), (2) &local_var produces a valid pointer to that local's heap location, (3) callee can read/write through the pointer. This is a significant memory model extension — locals are no longer just record fields. Study AutoCorres2's stack frame model.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 UnaryOperator & on local variables parsed
- [ ] #2 Locals that have address taken are heap-allocated in the model
- [ ] #3 Pointer to local is valid while the function executes
- [ ] #4 Callee can dereference pointer to caller's local
- [ ] #5 Stack frame cleanup: local's heap allocation freed on function return
- [ ] #6 Test: C function passing &local to another function
<!-- AC:END -->
