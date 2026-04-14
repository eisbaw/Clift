---
id: TASK-0138
title: Composed system-level correctness theorem
status: Done
assignee: []
created_date: '2026-04-10 18:45'
updated_date: '2026-04-10 19:53'
labels:
  - phase-l
  - verification
  - depth
  - milestone
dependencies:
  - TASK-0137
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Individual function correctness is not enough. seL4 proves a SYSTEM-LEVEL theorem: 'the kernel as a whole refines the abstract spec.' This means: any sequence of API calls on the C implementation produces results consistent with the abstract spec. Define: SystemExec (a sequence of operations), prove: for any SystemExec on the C implementation, the corresponding SystemExec on the abstract spec produces the same observable results. This composes all per-function proofs into one end-to-end guarantee.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 SystemExec type defined: sequence of operations
- [ ] #2 system_refinement theorem: C SystemExec refines abstract SystemExec
- [ ] #3 Proof uses per-function corres + FuncSpec composition
- [ ] #4 Example: 10-operation sequence on ring buffer produces same results as abstract queue
- [ ] #5 No sorry
<!-- AC:END -->
