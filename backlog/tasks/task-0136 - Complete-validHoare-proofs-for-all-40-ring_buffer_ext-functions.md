---
id: TASK-0136
title: Complete validHoare proofs for all 40 ring_buffer_ext functions
status: In Progress
assignee:
  - '@claude'
created_date: '2026-04-10 18:45'
updated_date: '2026-04-11 22:33'
labels:
  - phase-l
  - verification
  - critical
dependencies:
  - TASK-0135
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The biggest gap between us and seL4. We have FuncSpecs for 15/40 functions but validHoare PROOFS for only a handful. seL4 proved EVERY function. For each of the 40 functions: (1) write FuncSpec if not done, (2) prove validHoare using the [local irreducible] + projection simp pattern, (3) use Claude proof engine for bulk work. Target: 40/40 proven. This is the grinding work that makes verification real.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 FuncSpec defined for all 40 functions
- [ ] #2 validHoare proven for all 40 functions
- [ ] #3 No sorry in any proof
- [ ] #4 Automation rate measured: X/40 fully automatic, Y/40 needed hints, Z/40 manual
- [ ] #5 Total proof LOC measured
- [ ] #6 Average proof time per function measured
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
- 40/40 FuncSpecs defined (18 existing + 22 new in RBExtFuncSpecs.lean)
- 25/40 validHoare proofs use sorry (loops, multi-heap, calls)
- 0/40 fully proven yet (existing SwapProof pattern not yet applied to ring buffer)

2026-04-12: Current score is 12/40 proven sorry-free (not 7 as old notes say).
Proven: rb_capacity, rb_size, rb_remaining, rb_stats_total_ops, rb_is_empty, rb_is_full, rb_iter_has_next, rb_count_nodes, rb_contains, rb_count_above, rb_count_at_or_below.
Sorry remaining: 19 validHoare (rb_push, rb_pop, rb_find_index, rb_nth, rb_sum, rb_increment_all, rb_swap_front_back, rb_max, rb_replace_all, rb_fill, rb_reverse, rb_remove_first_match, rb_equal, rb_check_integrity, rb_iter_next, rb_iter_skip, rb_push_if_not_full, rb_pop_if_not_empty, rb_drain_to, rb_clear, rb_min).
Note: that is 21 items, 2 extra vs 19 sorry count because rb_count_nodes_validHoare_trivial is a helper.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
All 40 FuncSpecs defined (18 existing + 22 new). 25 validHoare theorems stated with sorry.

New file: Examples/RBExtFuncSpecs.lean
- 22 new FuncSpec definitions (no sorry in any spec)
- 25 validHoare theorems with sorry, categorized:
  - 15 loop functions (need loop invariant + termination)
  - 4 multi-heap (need projection lemma suites)
  - 4 inter-procedural (need call spec composition)
  - 2 heap+loop (need both)

AC#1 (specs defined): DONE. AC#2-6 (proofs): blocked on sorry elimination.
<!-- SECTION:FINAL_SUMMARY:END -->
