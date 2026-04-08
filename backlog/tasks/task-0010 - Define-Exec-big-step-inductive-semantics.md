---
id: TASK-0010
title: Define Exec big-step inductive semantics
status: Done
assignee:
  - '@mped'
created_date: '2026-04-08 21:34'
updated_date: '2026-04-08 22:50'
labels:
  - phase-0
  - csemantics
dependencies:
  - TASK-0007
references:
  - ext/AutoCorres2/c-parser/Simpl/Semantic.thy
  - ext/AutoCorres2/c-parser/Simpl/Termination.thy
  - Clift/CSemantics/Exec.lean
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Define big-step inductive execution relation following Simpl Semantic.thy. Inductive Prop (least fixed point) — non-terminating loops have no derivation. Include all CSimpl constructor rules. Define terminates predicate separately.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Exec inductive relation with rules for all 11 CSimpl constructors
- [x] #2 While rules: whileTrue and whileFalse
- [x] #3 Guard rules: guardOk and guardFault
- [x] #4 Call rule: procedure lookup and body execution
- [x] #5 terminates predicate as separate inductive
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Implemented Exec with 22 rules covering all 11 CSimpl constructors:
- skip (1 rule), basic (1), seq (3: normal/abrupt/fault), cond (2: true/false)
- while (4: true/false/abrupt/fault), call (2: defined/undefined)
- guard (2: ok/fault), throw (1), catch (3: normal/abrupt/fault)
- spec (2: normal/stuck), dynCom (1)

Terminates predicate has 16 rules mirroring the Exec structure.

Key design decisions:
- Fault propagation: seq, while, catch all propagate faults (faults are uncatchable)
- Call undefined = fault (matches Simpl)
- Spec stuck = fault (no related state means UB)
- Terminates for while requires body terminates AND recursive termination for all normal outcomes

All compiles, zero sorry.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Defined big-step inductive execution semantics in Clift/CSemantics/Exec.lean.

22 Exec rules covering all 11 CSimpl constructors with proper fault propagation.
16 Terminates rules as a separate inductive predicate.

Faithful to Simpl: non-termination = no derivation, faults propagate through seq/catch/while.
All kernel-checked, zero sorry.
<!-- SECTION:FINAL_SUMMARY:END -->
