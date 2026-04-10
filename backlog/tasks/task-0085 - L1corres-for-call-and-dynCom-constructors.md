---
id: TASK-0085
title: L1corres for call and dynCom constructors
status: To Do
assignee: []
created_date: '2026-04-10 05:17'
labels:
  - phase-b
  - lifting
dependencies: []
references:
  - ext/AutoCorres2/SimplConv.thy
  - ext/AutoCorres2/simpl_conv.ML
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Implement L1corres lemmas for CSimpl.call and CSimpl.dynCom. call looks up a procedure in ProcEnv and executes its body. dynCom captures the current state to set up call parameters. These are needed for multi-function C files. Study ext/AutoCorres2/SimplConv.thy for how AutoCorres2 handles procedure calls — it uses L1corres recursively on the looked-up body. The key challenge: mutual recursion between caller and callee.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 L1corres_call theorem proven: if body has L1corres, call has L1corres
- [ ] #2 L1corres_dynCom theorem proven: state-dependent command
- [ ] #3 Handles recursive functions (function calls itself)
- [ ] #4 Tested on a 2-function C file where one calls the other
- [ ] #5 No sorry
<!-- AC:END -->
