---
id: TASK-0085
title: L1corres for call and dynCom constructors
status: Done
assignee:
  - '@claude'
created_date: '2026-04-10 05:17'
updated_date: '2026-04-10 06:34'
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
- [x] #1 L1corres_call theorem proven: if body has L1corres, call has L1corres
- [x] #2 L1corres_dynCom theorem proven: state-dependent command
- [x] #3 Handles recursive functions (function calls itself)
- [x] #4 Tested on a 2-function C file where one calls the other
- [x] #5 No sorry
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Define L1.call combinator: given a ProcEnv mapping proc names to L1 bodies, look up and execute the L1 version
2. Prove L1corres_call: if Gamma p = some body and L1corres Gamma l1_body body, then L1corres Gamma (L1.call l1_env p) (CSimpl.call p)
3. Prove L1corres_dynCom: if for all s, L1corres Gamma (l1_f s) (f s), then L1corres Gamma (L1.dynCom l1_f) (CSimpl.dynCom f)
4. Update csimplToL1 in L1Auto.lean to handle call and dynCom constructors
5. Test with a 2-function C file
6. Build and verify no sorry
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
L1corres_call and L1corres_dynCom proved. L1Auto updated with two-pass approach: convert all bodies, build L1ProcEnv, prove L1corres. corres_auto tactic updated.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Implemented L1corres for call and dynCom. L1ProcEnv type + empty/insert, L1.call combinator (lookup + execute), L1.dynCom combinator (state-dependent command). L1corres_call and L1corres_dynCom theorems proved. L1Auto updated with two-pass approach (convert all, build L1ProcEnv, prove corres). corres_auto tactic handles dynCom; call corres left for manual proof. Tested on MultiCall (5-function C file).
<!-- SECTION:FINAL_SUMMARY:END -->
