---
id: TASK-0172
title: 'System initialization verification: boot code establishes invariants'
status: Done
assignee: []
created_date: '2026-04-10 18:53'
updated_date: '2026-04-10 23:22'
labels:
  - phase-l
  - seL4-parity
  - invariant
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
seL4 proved that kernel initialization (capDL layer) sets up a correct initial state that satisfies all global invariants. Every real system has initialization code that must establish the invariants that all subsequent proofs depend on. If init is wrong, all Hoare triples have unsatisfied preconditions. Need: (1) Framework for stating 'init establishes invariant I', (2) CImporter support for initialization functions (main/init entry points), (3) Example: ring_buffer_init establishes the ring buffer invariant, (4) Compose: init proof + operational proofs = full system correctness. Currently, our proofs assume invariants hold -- we never prove they are established.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Init verification framework: prove init function establishes invariant
- [ ] #2 ring_buffer_init proven to establish ring buffer abstract spec invariant
- [ ] #3 Composed theorem: init + operations = full system correctness
- [ ] #4 Pattern documented: how to verify initialization code
<!-- AC:END -->
