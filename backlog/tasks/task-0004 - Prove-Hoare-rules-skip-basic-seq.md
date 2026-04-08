---
id: TASK-0004
title: 'Prove Hoare rules: skip, basic, seq'
status: To Do
assignee: []
created_date: '2026-04-08 21:33'
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
- [ ] #1 hoare_skip: validHoare P skip P proven
- [ ] #2 hoare_basic: validHoare (fun s => Q (f s)) (basic f) Q proven
- [ ] #3 hoare_seq: composition rule proven
- [ ] #4 Corresponding totalHoare variants proven
- [ ] #5 All proofs use no sorry
<!-- AC:END -->
