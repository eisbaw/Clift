---
id: TASK-0174
title: 'Invariant preservation: prove every operation preserves global invariant'
status: To Do
assignee: []
created_date: '2026-04-10 18:53'
labels:
  - phase-l
  - seL4-parity
  - invariant
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
seL4 reports ~80% of proof effort goes to proving invariant preservation. TASK-0096 (Done) established the GlobalInvariant framework, but no task covers the systematic proof that EVERY operation in ring_buffer_ext (and future modules) preserves the global invariant. This is distinct from TASK-0136 (Hoare triples) -- Hoare triples prove functional correctness of individual operations. Invariant preservation proves the system stays in a good state across ALL operations. Need: (1) List all 40 ring_buffer_ext operations, (2) Prove each preserves the abstract spec invariant, (3) Compose into: 'from any valid state, any sequence of operations maintains the invariant'. This is the foundation that makes all other proofs composable.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 All 40 ring_buffer_ext operations listed
- [ ] #2 Each proven to preserve global invariant
- [ ] #3 Composed theorem: invariant preserved under arbitrary operation sequences
- [ ] #4 Pattern: how to add new operations and prove invariant preservation
<!-- AC:END -->
