---
id: TASK-0193
title: Eliminate 5 sorry in HashTableProof.lean
status: To Do
assignee: []
created_date: '2026-04-10 20:49'
updated_date: '2026-04-12 00:52'
labels:
  - sorry-elimination
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
5 validHoare sorry for hash table operations. Requires modular arithmetic reasoning and heap read/write.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 All 5 sorry eliminated
- [ ] #2 All proofs kernel-checked
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
2026-04-12: Reopened. Still has 4 sorry (was 5, 1 eliminated). HashTableProof.lean:107 (kernel depth), :131 (while loop), :136 (while loop), :152 (bitvec).

2026-04-12: Race 3 eliminated 2/4 sorry (ht_hash_correct, hash_index_bounded). Remaining 2 are while-loop proofs for linear probing — genuinely hard, need loop invariants.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Partially eliminated — see commit log. Remaining sorry are in init functions (multi-field heap writes), conditional heap reads, or loop-based functions requiring invariant machinery.
<!-- SECTION:FINAL_SUMMARY:END -->
