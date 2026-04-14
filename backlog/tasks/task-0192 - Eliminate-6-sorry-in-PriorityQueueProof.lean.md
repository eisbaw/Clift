---
id: TASK-0192
title: Eliminate 6 sorry in PriorityQueueProof.lean
status: To Do
assignee: []
created_date: '2026-04-10 20:49'
updated_date: '2026-04-11 22:34'
labels:
  - sorry-elimination
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
6 validHoare sorry for priority queue operations. Requires heap reasoning for array-based binary heap operations.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 All 6 sorry eliminated
- [ ] #2 All proofs kernel-checked
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
2026-04-12: Reopened. Still has 2 sorry. PriorityQueueProof.lean:260, :265 (both require call resolution for pq_bubble_up/down).
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Partially eliminated — see commit log. Remaining sorry are in init functions (multi-field heap writes), conditional heap reads, or loop-based functions requiring invariant machinery.
<!-- SECTION:FINAL_SUMMARY:END -->
