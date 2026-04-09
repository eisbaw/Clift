---
id: TASK-0053
title: Remove dead CError/CResult types from NondetM.lean
status: Done
assignee:
  - '@claude'
created_date: '2026-04-08 22:39'
updated_date: '2026-04-09 19:43'
labels:
  - cleanup
  - monadlib
dependencies: []
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
CError and CResult types are defined in NondetM.lean but never used. NondetM uses Prop-based failure, not typed errors. Remove the dead code to avoid confusion.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 CError and CResult removed from NondetM.lean
- [x] #2 lake build Clift succeeds after removal
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Removed dead CError and CResult types from NondetM.lean. These were initial design types replaced by NondetResult + Prop-based failure. No references existed elsewhere in the codebase. lake build succeeds.
<!-- SECTION:FINAL_SUMMARY:END -->
