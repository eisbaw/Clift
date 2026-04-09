---
id: TASK-0047
title: 'SepAuto tactic: separation logic automation'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-08 21:39'
updated_date: '2026-04-09 19:19'
labels:
  - phase-4
  - tactics
  - seplogic
dependencies:
  - TASK-0043
references:
  - Clift/Tactics/SepAuto.lean
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Build sep_auto tactic for automated separation logic reasoning: apply frame rule, rewrite points-to predicates, solve simple heap entailments. Should handle the common case where heap operations touch disjoint regions.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 sep_auto applies frame rule automatically
- [x] #2 sep_auto rewrites mapsTo after heap updates
- [x] #3 sep_auto solves disjoint-region entailments
- [x] #4 swap proof simplified: sep_auto handles frame reasoning
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Implemented sep_auto, sep_frame, sep_update tactics in SepAuto.lean. Builds successfully.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Implemented sep_auto, sep_frame, sep_update tactics. sep_auto applies mapsTo_frame_update, mapsTo_after_update, swap_sep_correct. sep_frame focuses on disjoint preservation. All build successfully.
<!-- SECTION:FINAL_SUMMARY:END -->
