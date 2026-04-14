---
id: TASK-0173
title: WCET / timing analysis integration for safety-critical deployment
status: To Do
assignee: []
created_date: '2026-04-10 18:53'
updated_date: '2026-04-14 22:11'
labels:
  - phase-n
  - seL4-parity
  - safety-critical
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
seL4 provided sound worst-case execution time (WCET) bounds for all system calls via static analysis of the binary. For safety-critical systems (automotive, aerospace, medical), timing bounds are mandatory (DO-178C, ISO 26262). Need: (1) Interface definition: how Clift proofs connect to WCET tools (e.g., aiT, Chronos), (2) Bounded-loop annotation framework (loop bounds needed for WCET), (3) Export verified loop bounds from Clift proofs to WCET tools, (4) Document: what timing properties can vs cannot be verified in Clift. This does not require implementing a WCET analyzer in Lean -- it requires providing the interface so external WCET tools can consume Clift's analysis.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Interface defined: how Clift loop bounds feed into WCET tools
- [ ] #2 Loop bound annotations extractable from termination proofs
- [ ] #3 Document: WCET integration architecture
- [ ] #4 Example: one function with exported loop bounds
<!-- AC:END -->
