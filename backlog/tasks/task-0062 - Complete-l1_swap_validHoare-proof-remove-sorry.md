---
id: TASK-0062
title: Complete l1_swap_validHoare proof (remove sorry)
status: To Do
assignee: []
created_date: '2026-04-09 06:43'
labels:
  - phase-3a
  - proof
dependencies: []
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The swap correctness proof in Examples/SwapProof.lean has one sorry in l1_swap_validHoare. This requires tracing through the L1 monadic set membership to show: (1) the computation doesn't fail when guards hold, (2) every ok-result has the swapped heap. The actual heap property (swap_values_exchanged) and L1corres are already sorry-free. This is mechanical but verbose; the Phase 4 c_vcg tactic should automate it.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 l1_swap_validHoare proved without sorry
- [ ] #2 swap_correct depends only on propext and Quot.sound
<!-- AC:END -->
