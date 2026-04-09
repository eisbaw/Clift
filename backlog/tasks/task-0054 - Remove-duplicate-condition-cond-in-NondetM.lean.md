---
id: TASK-0054
title: Remove duplicate condition/cond in NondetM.lean
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
NondetM.condition and NondetM.cond are identical functions (both branch on a state predicate). Remove one to avoid confusion. Keep cond since it matches CSimpl naming.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Only one conditional branching function remains in NondetM
- [x] #2 All references updated
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Removed NondetM.condition and its simp lemmas (condition_run_true, condition_run_false). Kept NondetM.cond which is the canonical version used by HoareRules, CStep, and CSimpl naming convention. L1.condition in SimplConv.lean is a separate function (different namespace, different type) and was left in place. lake build succeeds.
<!-- SECTION:FINAL_SUMMARY:END -->
