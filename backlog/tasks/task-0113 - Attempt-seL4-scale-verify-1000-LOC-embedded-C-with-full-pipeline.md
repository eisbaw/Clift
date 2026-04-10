---
id: TASK-0113
title: 'Attempt seL4-scale: verify 1000+ LOC embedded C with full pipeline'
status: To Do
assignee: []
created_date: '2026-04-10 12:58'
labels:
  - milestone
  - scalability
dependencies:
  - TASK-0105
  - TASK-0106
  - TASK-0107
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The ultimate test. Select a 1000+ LOC real embedded C codebase (RTOS scheduler core, crypto library, or protocol stack). Import with CImporter. Lift with clift. Write specs. Use MetaM VCG + Claude for proofs. Measure everything. This is the deliverable that proves Clift can match seL4's rigor at scale. Prerequisites: MetaM VCG (task-0105), array support (task-0106), mutual recursion (task-0107), enum/typedef/globals (task-0109). Without these, this task will identify exactly which gaps remain.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 1000+ LOC C codebase selected
- [ ] #2 CImporter processes all files (or documents what's missing)
- [ ] #3 clift lifts all functions (or documents failures)
- [ ] #4 Abstract spec written
- [ ] #5 At least 10 non-trivial functions fully verified
- [ ] #6 Proof-to-code ratio measured
- [ ] #7 Claude proof success rate measured
- [ ] #8 Gap analysis: what's still missing for seL4 parity?
<!-- AC:END -->
