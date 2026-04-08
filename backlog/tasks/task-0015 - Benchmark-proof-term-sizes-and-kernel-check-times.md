---
id: TASK-0015
title: 'Benchmark: proof term sizes and kernel check times'
status: To Do
assignee: []
created_date: '2026-04-08 21:35'
labels:
  - phase-0
  - test
  - risk-mitigation
dependencies:
  - TASK-0013
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Measure proof term size and kernel check time for max_correct and other Phase 0 proofs. Extrapolate to 100-line functions. If max_correct takes >5s to check, we need to redesign. Record measurements. This is risk mitigation for Risk #1 (proof term size).
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Proof term size for max_correct measured (bytes)
- [ ] #2 Kernel check time for max_correct measured (seconds)
- [ ] #3 grind tested on representative goals — success rate recorded
- [ ] #4 Extrapolation to 100-line function documented
- [ ] #5 Go/no-go assessment: can we proceed to Phase 1?
<!-- AC:END -->
