---
id: TASK-0007
title: Define Outcome type and CSimpl inductive
status: Done
assignee:
  - '@mped'
created_date: '2026-04-08 21:34'
updated_date: '2026-04-08 22:42'
labels:
  - phase-0
  - csemantics
dependencies: []
references:
  - ext/AutoCorres2/c-parser/Simpl/Language.thy
  - Clift/CSemantics/CSimpl.lean
  - Clift/CSemantics/Outcome.lean
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Define the Outcome type (normal/abrupt/fault) and the CSimpl deeply embedded imperative language. CSimpl must include all constructors from plan.md Decision 4: skip, basic, seq, cond, while, call, guard, throw, catch, spec, dynCom. Study ext/AutoCorres2/c-parser/Simpl/Language.thy for Simpl's original definition.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Outcome inductive with normal, abrupt, fault constructors compiles
- [x] #2 CSimpl inductive with all 11 constructors compiles
- [x] #3 CSimpl is parametric in state type σ
- [x] #4 dynCom constructor present (state-dependent command for function calls)
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Implemented Outcome (normal/abrupt/fault) and CSimpl with all 11 constructors.
CSimpl is parametric in σ. dynCom takes (σ → CSimpl σ).
guard uses (σ → Prop) not (σ → Bool) -- matches Simpl semantics.
Also implemented TypeTag, State (HeapRawState, Ptr), and ProcEnv.
ProcName is abbrev for String.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Implemented Outcome type and CSimpl inductive with all 11 constructors from plan.md Decision 4.

Files created/modified:
- Clift/CSemantics/Outcome.lean: Outcome with normal/abrupt/fault + helper functions
- Clift/CSemantics/CSimpl.lean: CSimpl inductive with skip/basic/seq/cond/while/call/guard/throw/catch/spec/dynCom
- Clift/CSemantics/ProcEnv.lean: ProcEnv type (ProcName -> Option CSimpl) with empty/insert/lookup
- Clift/CSemantics/TypeTag.lean: TypeTag structure for heap type descriptor
- Clift/CSemantics/State.lean: HeapRawState (mem + htd) and Ptr type

All compiles with lake build Clift.
<!-- SECTION:FINAL_SUMMARY:END -->
