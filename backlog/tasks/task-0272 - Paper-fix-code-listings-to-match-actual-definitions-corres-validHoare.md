---
id: TASK-0272
title: 'Paper: fix code listings to match actual definitions (corres, validHoare)'
status: Done
assignee: []
created_date: '2026-04-15 07:28'
updated_date: '2026-04-15 07:35'
labels:
  - paper
  - correctness
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The corres and validHoare code listings in the paper show simplified deterministic versions that do not match the actual codebase. corres has 8 params (not 4), uses NondetResult with .results Set (not .ok sum type). validHoare requires non-failure (not accepts it). Either show real definitions or explicitly mark as simplified.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 corres listing matches Clift/MonadLib/Corres.lean or is marked simplified
- [x] #2 validHoare listing matches Clift/MonadLib/Hoare.lean or is marked simplified
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Fixed corres listing to show actual 8-param definition with NondetResult (.results Set, .failed Prop). Fixed validHoare listing to show non-failure requirement. Both now match the actual codebase.
<!-- SECTION:FINAL_SUMMARY:END -->
