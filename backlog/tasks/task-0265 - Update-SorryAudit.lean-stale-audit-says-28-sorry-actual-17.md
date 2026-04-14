---
id: TASK-0265
title: 'Update SorryAudit.lean: stale audit (says 28 sorry, actual 17)'
status: In Progress
assignee:
  - '@claude'
created_date: '2026-04-14 20:53'
updated_date: '2026-04-14 22:05'
labels:
  - docs
  - stale
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Examples/SorryAudit.lean dated 2026-04-08 says 28 sorry. Actual is 17 (per Python audit). The sorry have been restructured across more files (DrainTo, PriorityQueue, RBExtRefinement). The detailed inventory table is wrong.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Executive summary matches current sorry count
- [x] #2 Detailed inventory covers all files with sorry
- [x] #3 Blocked-by relationships are correct
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Updated SorryAudit.lean: 28->17 sorry, restructured across 5 files (PriorityQueueProof, RBExtProofRbDrainTo, RBExtProofsLoops, RBExtProofsLoops2, RBExtRefinement). Added severity subcategories: 4 tautological, 8 inter-procedural, 3 blocked refinement, 2 guard-chain.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Updated SorryAudit.lean to match actual sorry count of 17 (down from 28). The file now accurately reflects the current distribution across 5 files, with correct line numbers, theorem names, categories, and blocked-by relationships. Added references to TASK-0231 (tautological specs) and TASK-0235 (dynCom call rule) as blockers.
<!-- SECTION:FINAL_SUMMARY:END -->
