---
id: TASK-0264
title: 'Update README.md: stale sorry count (says 27, actual 42) and stale task count'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-14 20:53'
updated_date: '2026-04-14 22:03'
labels:
  - docs
  - stale
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
README.md Status section has stale numbers. Sorry count says 27 but actual is 17 (per Python audit). Task done count says 215+ but is higher. Also ring_buffer_ext refinement says 21/40 which may be outdated.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Sorry count matches just sorry-count output
- [x] #2 Task done count matches backlog task list -s Done count
- [x] #3 Refinement progress matches actual RBExtRefinement state
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Updated sorry count 27->17, task done count 215->218, refinement progress 21/40->27/40. All numbers verified against audit.py and backlog CLI.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Updated README.md Status and Key proofs sections with correct numbers: sorry count 27->17 (verified via audit.py), backlog tasks done 215+->218 (verified via backlog CLI), ring_buffer_ext refinement 21/40->27/40 (verified by counting sorry-free validHoare theorems across RBExt proof files).
<!-- SECTION:FINAL_SUMMARY:END -->
