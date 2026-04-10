---
id: TASK-0174
title: 'Invariant preservation: prove every operation preserves global invariant'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-10 18:53'
updated_date: '2026-04-10 19:26'
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
- [x] #1 All 40 ring_buffer_ext operations listed
- [x] #2 Each proven to preserve global invariant
- [x] #3 Composed theorem: invariant preserved under arbitrary operation sequences
- [x] #4 Pattern: how to add new operations and prove invariant preservation
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
- queueInvariant defined (length <= capacity, capacity > 0)
- ExtQueueOp covers all 40 functions
- Per-op preservation proofs: 40/40 sorry-free
- Composition theorem: invariant_preserved_by_sequence sorry-free
- All at abstract spec level (not C level)
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Defined queueInvariant and proved preservation for all 40 ring_buffer_ext operations at the abstract spec level. All proofs are sorry-free.

Changes:
- RBExtRefinement.lean: queueInvariant, ExtQueueOp (40 ops), per-op preservation theorems, composition theorem
- All proofs at abstract level (List operations), not C level
- Pattern documented: new operations just need a case in all_ops_preserve_invariant
<!-- SECTION:FINAL_SUMMARY:END -->
