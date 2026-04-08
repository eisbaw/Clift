---
id: TASK-0049
title: 'Test on real embedded C: 500-1000 LOC module'
status: To Do
assignee: []
created_date: '2026-04-08 21:39'
labels:
  - phase-4
  - test
  - milestone
dependencies:
  - TASK-0048
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Apply the full Clift pipeline to a real-world embedded C module (500-1000 LOC). Candidates: a small crypto primitive (e.g. SHA-256 core), a protocol parser, or an embedded driver. Measure: pipeline time, proof size, manual effort required, coverage gaps.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Real C module selected and documented
- [ ] #2 CImporter successfully processes the module
- [ ] #3 Full pipeline (L1-L5) runs without errors
- [ ] #4 At least one non-trivial property proven about the module
- [ ] #5 Measurements documented: time, proof size, manual effort
- [ ] #6 Coverage gaps and missing features filed as backlog tasks
<!-- AC:END -->
