---
id: TASK-0201
title: Eliminate 2 sorry in UartDriverProof.lean
status: To Do
assignee: []
created_date: '2026-04-10 20:50'
updated_date: '2026-04-11 22:34'
labels:
  - sorry-elimination
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
2 sorry: one requires heap write reasoning for 11 field assignments, one requires heap read + field projection.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 All 2 sorry eliminated
- [ ] #2 All proofs kernel-checked
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
2026-04-12: Reopened. Still has 1 sorry. UartDriverProof.lean:127 (11-field heap write).
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Partially eliminated — see commit log. Remaining sorry are in init functions (multi-field heap writes), conditional heap reads, or loop-based functions requiring invariant machinery.
<!-- SECTION:FINAL_SUMMARY:END -->
