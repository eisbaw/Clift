---
id: TASK-0221
title: Prove rb_push validHoare using guard_modify chain lemmas
status: Done
assignee: []
created_date: '2026-04-11 15:07'
updated_date: '2026-04-12 05:28'
labels:
  - sorry-elimination
  - ring-buffer
dependencies:
  - TASK-0220
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
rb_push is an 8-step guard+modify chain: guard(valid rb) -> read count -> guard(count < cap) -> read head -> alloc node -> write node.val -> write node.next -> write rb.head -> write rb.count -> throw -> catch -> skip. After strengthening preconditions (task-0220), use L1_hoare_guard_modify_chain3 or a 4+ step variant. Each step's projection lemmas need [local irreducible] hVal heapUpdate. The composed function f = f8 ∘ f7 ∘ ... ∘ f1 must stay opaque until the postcondition check, where simp + hVal_heapUpdate_same/disjoint close it. Pattern: define step functions with anonymous constructors, prove projections as rfl, chain with L1_hoare_guard_modify_fused.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 rb_push_validHoare proven with zero sorry
- [ ] #2 Uses [local irreducible] hVal heapUpdate throughout
- [ ] #3 Projection simp lemmas for each step function
- [ ] #4 Postcondition discharged via hVal_heapUpdate_same/disjoint + ptrDisjoint
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Blocker identified: rb_push has 8+ guard+modify steps with heap writes. Each heapUpdate changes the heap, so subsequent heapPtrValid guards need ptrDisjoint to show validity preserved.

Approach: define each step as anonymous-constructor function, prove two-step projection lemmas, chain with L1_guard_modify_result + L1_seq_singleton_ok. Need ptrDisjoint(new_node, rb_state) in precondition.

AutoCorres2 insight: their L1_merge_assignments fuses consecutive modifies. Our equivalent: L1_guard_modify_guard_modify_result chains 2 pairs. Need chain4/chain5 for rb_push.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
rb_push_validHoare proven using chain4/5 + compose infrastructure. 8 step functions with anonymous constructors. Precondition strengthened with ptrDisjoint. Build clean.
<!-- SECTION:FINAL_SUMMARY:END -->
