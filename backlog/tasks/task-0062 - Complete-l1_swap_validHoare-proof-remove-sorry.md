---
id: TASK-0062
title: Complete l1_swap_validHoare proof (remove sorry)
status: In Progress
assignee: []
created_date: '2026-04-09 06:43'
updated_date: '2026-04-09 16:23'
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

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Attempted proof. Hits Lean 4 kernel deep recursion limit. The L1.seq/guard/modify chains create nested structure updates that exceed the kernel hardcoded depth. Need c_vcg tactic (Phase 4) or flatter L1 definitions.

Gotcha: Lean 4 {s with ...} desugars to 'have __src := s.field' in some contexts and 'let __src := s.field' in others. These are NOT definitionally equal for non-Prop types. This blocks the swap validHoare proof because L1_guard_modify_result produces terms with 'let' form but the l1_swap_body definition (via unfold) produces 'have' form. The L1 Hoare rules (L1_hoare_guard, L1_hoare_modify, L1_hoare_seq_ok, L1_hoare_catch_ok etc.) are proved and correct, but composing them for swap hits kernel deep recursion. Direct set-membership proof hits have/let mismatch. Fix needed: normalize {s with ...} desugaring, or use a tactic that handles this (omega-style), or redefine l1_swap_body with explicit let bindings.

L1 Hoare rules committed (L1_hoare_skip, L1_hoare_modify, L1_hoare_guard, L1_hoare_seq, L1_hoare_catch, L1_hoare_seq_ok, L1_hoare_catch_ok, L1_hoare_guard', L1_hoare_modify', L1_hoare_pre). Sorry still present in l1_swap_validHoare. Next step: write a VCG tactic that normalizes {s with ...} desugaring before applying the rules, or redefine l1_swap_body with explicit anonymous constructors.
<!-- SECTION:NOTES:END -->
