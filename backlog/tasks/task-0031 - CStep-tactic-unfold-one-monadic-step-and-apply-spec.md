---
id: TASK-0031
title: 'CStep tactic: unfold one monadic step and apply spec'
status: To Do
assignee: []
created_date: '2026-04-08 21:37'
labels:
  - phase-2
  - tactics
dependencies:
  - TASK-0025
references:
  - ext/AutoCorres2/AutoCorresSimpset.thy
  - Clift/Tactics/CStep.lean
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Build the c_step tactic (analogous to Aeneas's progress tactic). When invoked on a monadic goal, it unfolds one bind step, applies the function's specification, and leaves the user with the precondition obligation. This is the primary user-facing proof tool.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 c_step tactic unfolds bind and applies function spec
- [ ] #2 Works on validHoare goals
- [ ] #3 Works on totalHoare goals
- [ ] #4 Tested on gcd proof: reduces proof from N lines to simpler steps
<!-- AC:END -->
