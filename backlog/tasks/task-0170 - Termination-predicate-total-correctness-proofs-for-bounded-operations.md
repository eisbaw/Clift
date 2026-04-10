---
id: TASK-0170
title: 'Termination predicate: total correctness proofs for bounded operations'
status: To Do
assignee: []
created_date: '2026-04-10 18:53'
labels:
  - phase-l
  - soundness
  - seL4-parity
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
seL4 proved all kernel operations terminate (bounded execution). Clift's Exec semantics only give partial correctness (non-termination = no derivation). Need: (1) Define 'terminates' inductive predicate following Simpl's Terminates.thy, (2) Define totalHoare as validHoare + termination, (3) Prove termination for all ring_buffer_ext functions (they are all bounded), (4) Establish the pattern: partial correctness + termination = total correctness. Without this, we cannot prove liveness or progress -- a function could satisfy its Hoare triple by simply never returning. seL4 parity REQUIRES total correctness for all verified functions.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Terminates inductive predicate defined following Simpl
- [ ] #2 totalHoare combines partial correctness + terminates
- [ ] #3 At least 5 ring_buffer_ext functions proven to terminate
- [ ] #4 Pattern documented: how to prove total correctness
<!-- AC:END -->
