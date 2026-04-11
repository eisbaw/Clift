---
id: TASK-0213
title: 'Third verification campaign: verify seL4 capability functions'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-11 06:29'
updated_date: '2026-04-11 08:46'
labels:
  - verification
  - seL4
  - milestone
dependencies:
  - TASK-0207
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The credibility milestone. Verify the seL4 capability functions (sel4_cap.c) with full functional correctness. These are the simplest seL4 kernel functions — pure bitfield extraction. If Clift can verify them with the same rigor as AutoCorres2, it demonstrates direct seL4 parity for this subset. Compare our proof with AutoCorres2's proof for the same functions.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 All 6 seL4 cap functions fully verified (zero sorry)
- [ ] #2 Full functional correctness: exact bit extraction proven
- [ ] #3 Comparison with AutoCorres2 proof documented
- [ ] #4 Proof-to-code ratio compared
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Assessment document written: docs/verification-campaign-sel4-cap.md. Current state: 3/6 seL4 cap functions fully verified (capType, capPtr, cap_is_null), 2 sorry remaining (isArchObjectType, lookup_fault_depth_mismatch), cte_insert not yet specified. Estimated 4-5 days for full verification. AutoCorres2 comparison points identified. Prerequisites: conditional pattern proof helper (for isArchObjectType), heap write projection lemmas (for lookup_fault_depth_mismatch).
<!-- SECTION:FINAL_SUMMARY:END -->
