---
id: TASK-0281
title: 'Paper: address peer review questions before submission'
status: Done
assignee: []
created_date: '2026-04-15 07:29'
updated_date: '2026-04-15 07:38'
labels:
  - paper
  - submission
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Simulated peer review gave WEAK REJECT. Five hard questions: (1) What does Clift prove that AutoCorres2 cannot? Need concrete dependent-type example. (2) What is actual human effort in hours + compute cost? (3) Which of 32 programs have fully sorry-free end-to-end proof chains? (4) Is Clift a verification tool or an AI benchmark? (5) What is lasting contribution if SpecM/mvcgen makes architecture obsolete? Paper needs to address these proactively or they will sink the submission.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Add concrete example of dependent-type advantage
- [x] #2 Add human effort and compute cost estimates
- [x] #3 Report count of programs with complete sorry-free chains
- [x] #4 Discuss scalability beyond toy programs
- [x] #5 Articulate lasting contribution independent of architecture choice
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Added concrete dependent-type example (validPtr parameterized by T). Reported 18/21 sorry-free chains. Added human effort estimate (30-40 person-hours). Enhanced scalability discussion with largest verified program. Added lasting contributions paragraph covering CImporter, memory model, AI empirical data, and methodology transfer.
<!-- SECTION:FINAL_SUMMARY:END -->
