---
id: TASK-0058
title: Add Guard fault-set parameter for UB tracking
status: Done
assignee:
  - '@claude'
created_date: '2026-04-08 22:55'
updated_date: '2026-04-09 22:36'
labels:
  - enhancement
  - csemantics
dependencies: []
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Simpl's Guard constructor takes a fault-set parameter f that identifies WHICH guard failed. Our guard just produces a plain fault with no identifier. Not needed for soundness but useful for debugging and error reporting. Low priority for Phase 0.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 ADR documenting the decision to defer fault-set parameter
- [x] #2 Code comment in CSimpl.lean referencing the ADR
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Created ADR-006 documenting the decision to defer the guard fault-set parameter. Added code comment to CSimpl.lean. Fault-set is not needed while proving total fault-freedom; recommended for Phase 4 automation.
<!-- SECTION:FINAL_SUMMARY:END -->
