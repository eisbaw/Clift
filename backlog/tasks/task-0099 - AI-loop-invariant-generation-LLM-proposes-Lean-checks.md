---
id: TASK-0099
title: 'AI loop invariant generation: LLM proposes, Lean checks'
status: To Do
assignee: []
created_date: '2026-04-10 05:19'
labels:
  - phase-e
  - ai
  - automation
dependencies:
  - TASK-0098
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The single highest-value AI integration point. Given a while loop body + precondition + postcondition, have an LLM propose a loop invariant. The invariant is checked by Lean (kernel-verified). If it fails, feed the error back to the LLM for refinement. This is the 80% problem in verification — invariants dominate proof effort. The VCG (task-0087) generates invariant obligations; this task fills them with AI.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 ai_invariant tactic: serialize loop context, call LLM, check result
- [ ] #2 Retry logic: on failure, feed error + goal state back to LLM (up to 5 retries)
- [ ] #3 Tested on gcd while loop invariant
- [ ] #4 Tested on list traversal loop invariant
- [ ] #5 Measured: success rate on test suite (target >60%)
- [ ] #6 All accepted invariants kernel-checked (AI is untrusted)
<!-- AC:END -->
