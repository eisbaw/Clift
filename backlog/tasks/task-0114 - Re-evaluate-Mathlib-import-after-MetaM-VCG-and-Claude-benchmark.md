---
id: TASK-0114
title: Re-evaluate Mathlib import after MetaM VCG and Claude benchmark
status: To Do
assignee:
  - '@claude'
created_date: '2026-04-10 13:07'
updated_date: '2026-04-14 22:12'
labels:
  - infrastructure
  - deferred-decision
dependencies:
  - TASK-0105
  - TASK-0112
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
After task-0105 (MetaM VCG) eliminates the L1 stepping bottleneck and task-0112 (Claude benchmark) reveals what proof patterns Claude struggles with, re-evaluate whether Mathlib should be re-imported. Key questions: (1) Does Claude need Mathlib lemmas to write proofs? (2) Would grind + Mathlib @[grind] lemmas close goals our custom tactics cannot? (3) Does the remaining proof effort (after MetaM VCG) shift to arithmetic/data structures where Mathlib helps? If yes to any: re-import with prebuilt cache (lake exe cache get) and measure RAM impact. If no: keep out permanently.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Task-0105 (MetaM VCG) and task-0112 (Claude benchmark) are both Done
- [x] #2 Remaining proof effort categorized: what % is arithmetic? data structures? L1 stepping?
- [x] #3 Claude's failure patterns analyzed: does Mathlib fix them?
- [ ] #4 If re-importing: RAM measured with prebuilt cache on target machine
- [x] #5 Decision documented as ADR update to ADR-002
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
AC #1 partial: task-0112 is Done, task-0105 is In Progress (partially done). The re-evaluation proceeds with available data since task-0105 partial results are sufficient for the Mathlib decision.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Re-evaluated Mathlib import based on task-0112 benchmark data.

Decision: KEEP OUT permanently.

Analysis:
- Claude 85% first-attempt success WITHOUT Mathlib, 100% with retries
- Failure patterns are Clift-domain-specific (set idioms, irreducibility hints, constructor names), not math-library gaps
- Remaining proof effort: 50% heap reasoning, 25% loop invariants, 15% abstract spec, 10% set/NondetM
- Only the 15% abstract spec could benefit from Mathlib, and omega + inline lemmas cover it
- RAM savings (500MB vs 9GB+) and build time savings (25s vs 10min+) are worth more

ADR-002 updated with re-evaluation section.
AC #1 partially met: task-0105 is In Progress, task-0112 is Done.
AC #4 not applicable (decision is keep out, not re-import).
<!-- SECTION:FINAL_SUMMARY:END -->
