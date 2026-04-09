---
id: TASK-0057
title: Add Stuck outcome or document merge-into-fault decision
status: Done
assignee:
  - '@claude'
created_date: '2026-04-08 22:55'
updated_date: '2026-04-09 22:36'
labels:
  - design
  - csemantics
dependencies: []
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Simpl has 4 outcomes: Normal, Abrupt, Fault, Stuck. Our Outcome has 3, merging Stuck into fault. This is a deliberate simplification. Either add Stuck as a separate outcome (cleaner separation of UB vs stuck) or document the merge as an ADR.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 ADR documenting the Stuck/fault merge decision
- [x] #2 Code comment in Outcome.lean referencing the ADR
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Created ADR-005 documenting the decision to merge Simpl's Stuck outcome into fault. Added code comment to Outcome.lean explaining the rationale: both represent UB in C, our ProcEnv is total, fewer proof cases.
<!-- SECTION:FINAL_SUMMARY:END -->
