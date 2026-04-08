---
id: TASK-0048
title: 'corres_auto tactic: correspondence proof automation'
status: To Do
assignee: []
created_date: '2026-04-08 21:39'
labels:
  - phase-4
  - tactics
dependencies:
  - TASK-0045
references:
  - ext/AutoCorres2/CorresXF.thy
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Build corres_auto tactic that handles the formulaic parts of correspondence proofs between lifting stages. Should unfold definitions, apply simulation lemmas, and discharge side conditions. Target: close 70% of correspondence obligations automatically.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 corres_auto unfolds corres goal and applies structural lemmas
- [ ] #2 Handles skip, basic, seq, cond correspondence automatically
- [ ] #3 Falls back to user for while/loop correspondence
- [ ] #4 Measured: what % of obligations does it close?
<!-- AC:END -->
