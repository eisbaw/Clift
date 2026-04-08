---
id: TASK-0013
title: Hand-write CSimpl for max() and prove Hoare triple
status: To Do
assignee: []
created_date: '2026-04-08 21:35'
labels:
  - phase-0
  - test
dependencies:
  - TASK-0005
  - TASK-0010
  - TASK-0011
references:
  - test/c_sources/max.c
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Manually encode uint32_t max(uint32_t a, uint32_t b) { return a > b ? a : b; } as a CSimpl term with a concrete CState. Prove validHoare about it. This is the first end-to-end test that MonadLib + CSemantics work together. No CImporter — hand-written CSimpl.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 max_body : CSimpl MaxState defined and compiles
- [ ] #2 MaxState structure with a, b locals defined
- [ ] #3 theorem max_correct : validHoare ... max_body ... proven and kernel-checked
- [ ] #4 Proof uses Hoare rules from tasks 0004-0005, no sorry
- [ ] #5 Proof term size measured and recorded in implementation notes
<!-- AC:END -->
