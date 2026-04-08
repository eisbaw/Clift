---
id: TASK-0007
title: Define Outcome type and CSimpl inductive
status: To Do
assignee: []
created_date: '2026-04-08 21:34'
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
- [ ] #1 Outcome inductive with normal, abrupt, fault constructors compiles
- [ ] #2 CSimpl inductive with all 11 constructors compiles
- [ ] #3 CSimpl is parametric in state type σ
- [ ] #4 dynCom constructor present (state-dependent command for function calls)
<!-- AC:END -->
