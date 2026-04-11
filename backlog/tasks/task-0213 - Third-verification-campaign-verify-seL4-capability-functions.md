---
id: TASK-0213
title: 'Third verification campaign: verify seL4 capability functions'
status: To Do
assignee: []
created_date: '2026-04-11 06:29'
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
