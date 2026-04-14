---
id: TASK-0209
title: 'Proof engine: learn from failures to improve retry prompts'
status: To Do
assignee:
  - '@claude'
created_date: '2026-04-11 06:29'
updated_date: '2026-04-14 22:11'
labels:
  - proof-engine
  - ai
dependencies:
  - TASK-0205
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
When Claude's proof fails, the error message contains valuable information (wrong lemma name, type mismatch, unsolved goal). Feed this back to Claude in the retry prompt with: (1) the original goal, (2) the attempted proof, (3) the error, (4) analysis of what went wrong. This should increase retry success rate from ~15% to ~30% additional.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Error parsing: extract Lean error type (type mismatch, unsolved goal, unknown identifier)
- [ ] #2 Retry prompt includes: original attempt + error + analysis
- [ ] #3 Measured: retry success rate improvement
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Design spec written: docs/proof-engine-failure-learning.md. Covers 5 error categories (unknown_id, type_mismatch, unsolved_goals, tactic_failed, timeout), structured error parsing, retry prompt template with old attempt + error + analysis, 3-retry strategy (error correction, alternative approach, simplified goal). No code implementation -- this is a design task.
<!-- SECTION:FINAL_SUMMARY:END -->
