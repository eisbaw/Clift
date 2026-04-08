---
id: TASK-0047
title: 'SepAuto tactic: separation logic automation'
status: To Do
assignee: []
created_date: '2026-04-08 21:39'
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
- [ ] #1 sep_auto applies frame rule automatically
- [ ] #2 sep_auto rewrites mapsTo after heap updates
- [ ] #3 sep_auto solves disjoint-region entailments
- [ ] #4 swap proof simplified: sep_auto handles frame reasoning
<!-- AC:END -->
