---
id: TASK-0046
title: 'CVcg tactic: verification condition generator'
status: To Do
assignee: []
created_date: '2026-04-08 21:39'
labels:
  - phase-4
  - tactics
dependencies:
  - TASK-0045
references:
  - ext/AutoCorres2/AutoCorresSimpset.thy
  - Clift/Tactics/CVcg.lean
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Build the c_vcg tactic that applies Hoare rules automatically, decomposes sequential programs into leaf obligations. Should handle: seq, cond, while (with user-supplied invariant), assignment, pointer read/write. Leaves only the interesting proof obligations for the user/AI.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 c_vcg decomposes sequential monadic programs into leaf goals
- [ ] #2 Handles bind, if, match on conditionals
- [ ] #3 Applies function specs for known functions
- [ ] #4 Requires user-supplied loop invariants (via annotation or parameter)
- [ ] #5 Tested: gcd proof reduced to invariant + termination obligations only
<!-- AC:END -->
