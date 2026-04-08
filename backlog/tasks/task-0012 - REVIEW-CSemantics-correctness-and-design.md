---
id: TASK-0012
title: 'REVIEW: CSemantics correctness and design'
status: To Do
assignee: []
created_date: '2026-04-08 21:35'
labels:
  - review
  - phase-0
dependencies:
  - TASK-0011
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
MPED architecture review of CSemantics (tasks 0007-0011). Verify: CSimpl constructors match Simpl's Language.thy, Exec rules are faithful to Semantic.thy, terminates is correctly defined, state record design matches seL4's one-record approach. Check for missing Exec rules or incorrect rule shapes.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 CSimpl constructors verified against ext/AutoCorres2/c-parser/Simpl/Language.thy
- [ ] #2 Exec rules verified against ext/AutoCorres2/c-parser/Simpl/Semantic.thy
- [ ] #3 terminates predicate verified against Termination.thy
- [ ] #4 State design reviewed for per-function state type problem
- [ ] #5 Gaps identified and filed as backlog tasks
<!-- AC:END -->
