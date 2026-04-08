---
id: TASK-0019
title: 'CImporter: emit CSimpl function bodies'
status: To Do
assignee: []
created_date: '2026-04-08 21:35'
labels:
  - phase-1
  - cimporter
dependencies:
  - TASK-0018
references:
  - ext/AutoCorres2/c-parser/
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Emit CSimpl terms for each function body. Handle: assignments (basic), if/else (cond), while loops (while), return (throw), arithmetic (+,-,*,/,%), comparisons (<,>,<=,>=,==,!=), bitwise (&,|,^,<<,>>). Each operation on signed integers gets a guard for overflow (UB). Emit ProcEnv mapping function names to bodies.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Assignments emit CSimpl.basic with state update
- [ ] #2 if/else emits CSimpl.cond
- [ ] #3 while emits CSimpl.while
- [ ] #4 return emits CSimpl.throw (caught by function-level catch)
- [ ] #5 Signed arithmetic gets CSimpl.guard for overflow
- [ ] #6 ProcEnv emitted mapping all function names to bodies
- [ ] #7 Generated .lean compiles
<!-- AC:END -->
