---
id: TASK-0081
title: 'MetaM L2 LocalVarExtract: auto-extract locals to lambda params'
status: To Do
assignee: []
created_date: '2026-04-10 05:17'
labels:
  - phase-a
  - metam
  - automation
dependencies:
  - TASK-0080
references:
  - ext/AutoCorres2/local_var_extract.ML
  - ext/AutoCorres2/LocalVarExtract.thy
  - Clift/Lifting/LocalVarExtract.lean
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Port AutoCorres2's local_var_extract.ML to Lean 4 MetaM. Given an L1 function that reads/writes locals from the CState.locals record, automatically generate an L2 version where locals are lambda-bound Lean parameters. Generate L2corres proof. After L2, functions look natural — no ugly globals+locals state record. Currently L2 is a manual stub (Clift/Lifting/LocalVarExtract.lean).
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 MetaM command 'clift_l2' transforms L1 functions to L2 form
- [ ] #2 Locals extracted as explicit function parameters
- [ ] #3 L2corres proof generated automatically
- [ ] #4 State type after L2 contains only globals (no locals record)
- [ ] #5 Tested on gcd (3 locals: a, b, t) and swap (3 locals: a, b, t)
- [ ] #6 No sorry
<!-- AC:END -->
