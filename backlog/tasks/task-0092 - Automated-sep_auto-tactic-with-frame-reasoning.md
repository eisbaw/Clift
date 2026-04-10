---
id: TASK-0092
title: Automated sep_auto tactic with frame reasoning
status: To Do
assignee: []
created_date: '2026-04-10 05:18'
labels:
  - phase-c
  - tactics
  - seplogic
dependencies:
  - TASK-0090
  - TASK-0091
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Build a production-quality sep_auto tactic that handles: (1) applying the frame rule using modifies-set information, (2) rewriting mapsTo assertions after heap updates, (3) sep_comm/sep_assoc normalization, (4) entailment checking for simple heap predicates. Should handle 80%+ of separation logic obligations automatically. Currently sep_auto is just simp lemmas.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 sep_auto applies frame rule automatically using modifies-set
- [ ] #2 sep_auto rewrites mapsTo after heapUpdate
- [ ] #3 sep_auto normalizes separating conjunctions
- [ ] #4 Handles pointer disjointness reasoning
- [ ] #5 Measured: closes 80%+ of sep logic goals in test suite
- [ ] #6 Tested on swap, list traversal, struct access
<!-- AC:END -->
