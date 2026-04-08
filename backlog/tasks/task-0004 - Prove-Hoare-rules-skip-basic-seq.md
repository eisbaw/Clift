---
id: TASK-0004
title: 'Prove Hoare rules: skip, basic, seq'
status: Done
assignee:
  - '@mped'
created_date: '2026-04-08 21:33'
updated_date: '2026-04-08 22:35'
labels:
  - phase-0
  - monadlib
dependencies:
  - TASK-0003
references:
  - ext/AutoCorres2/L1Defs.thy
  - Clift/MonadLib/HoareRules.lean
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Prove the sequential Hoare logic rules for skip (no-op), basic (state update), and seq (sequential composition). These are the building blocks for all verification. Study ext/AutoCorres2/L1Defs.thy for the seL4 equivalents.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 hoare_skip: validHoare P skip P proven
- [x] #2 hoare_basic: validHoare (fun s => Q (f s)) (basic f) Q proven
- [x] #3 hoare_seq: composition rule proven
- [x] #4 Corresponding totalHoare variants proven
- [x] #5 All proofs use no sorry
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
All rules proven for both validHoare and totalHoare. Also added hoare_seq' (simplified seq for unit), hoare_consequence, hoare_strengthen_pre, hoare_weaken_post, hoare_conj, and hoare_bind.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Proved hoare_skip, hoare_basic, hoare_seq (and hoare_seq' simplified form) plus total correctness variants total_hoare_skip, total_hoare_basic, total_hoare_seq in Clift/MonadLib/HoareRules.lean. Also added hoare_bind for general monadic sequencing. No sorry.
<!-- SECTION:FINAL_SUMMARY:END -->
