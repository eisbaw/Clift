---
id: TASK-0010
title: Define Exec big-step inductive semantics
status: To Do
assignee: []
created_date: '2026-04-08 21:34'
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
- [ ] #1 Exec inductive relation with rules for all 11 CSimpl constructors
- [ ] #2 While rules: whileTrue and whileFalse
- [ ] #3 Guard rules: guardOk and guardFault
- [ ] #4 Call rule: procedure lookup and body execution
- [ ] #5 terminates predicate as separate inductive
<!-- AC:END -->
