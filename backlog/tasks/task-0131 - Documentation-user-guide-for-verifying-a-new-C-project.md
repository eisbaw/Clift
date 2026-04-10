---
id: TASK-0131
title: 'Documentation: user guide for verifying a new C project'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-10 15:30'
updated_date: '2026-04-10 18:34'
labels:
  - phase-j
  - documentation
  - industrial
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
For adoption: a step-by-step guide. (1) How to set up Clift for a new C project, (2) how to run CImporter, (3) how to write abstract specs, (4) how to write function specs, (5) how to use clift + VCG + sep_auto, (6) how to invoke Claude for proofs, (7) common pitfalls and solutions. Include a worked example from scratch: take a 100-LOC C module through full verification.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 User guide written as docs/user-guide.md
- [x] #2 Worked example: 100-LOC C module verified from scratch
- [x] #3 Troubleshooting section: common errors and fixes
- [x] #4 Quick-start: verify first function in <30 minutes
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
User guide (docs/user-guide.md): quick start in 8 steps, worked example with bounded counter module (100+ LOC C verified from scratch), troubleshooting section with 8 common errors, pipeline explanation, specification writing guide.
<!-- SECTION:FINAL_SUMMARY:END -->
