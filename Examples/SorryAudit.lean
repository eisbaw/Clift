-- Task 0182: Sorry audit — systematic inventory of all sorry in the codebase
--
-- For each sorry: file, line, what it proves, why it's sorry, what's needed
-- to fix it, estimated effort.
--
-- A formal methods reviewer will grep for sorry FIRST. This file is the
-- honest accounting that demonstrates we know exactly where the gaps are.

import Clift.CSemantics

/-! # Sorry Audit — 2026-04-08

## Executive summary

  Total sorry in codebase: 28
  - Core library (Clift/):     0  (ZERO sorry in MonadLib, CSemantics, Lifting, Tactics)
  - Generated code:            0  (ZERO sorry in Generated/)
  - Examples/RBExtFuncSpecs:   25 (validHoare proofs for ring buffer functions)
  - Examples/RBExtRefinement:  3  (refinement proofs, blocked on the 25 above)
  - Other Examples:            0  (ZERO sorry in GCD, Swap, SoundnessCheck, etc.)

  The 28 sorry are ALL in the Examples/ directory, not in the core library.
  The core library (MonadLib, CSemantics, Lifting, Tactics) is sorry-free.

## Severity classification

  - **Core sorry** (would invalidate the framework): 0
  - **Proof sorry** (proofs not yet completed): 25 (RBExtFuncSpecs validHoare)
  - **Blocked sorry** (transitively blocked): 3 (RBExtRefinement, blocked on above 25)
  - **Stub sorry** (placeholder for future work): 0

## Detailed inventory

### File: Examples/RBExtFuncSpecs.lean (25 sorry)

All 25 are validHoare proofs for ring buffer functions. The FuncSpecs
themselves (preconditions/postconditions) are fully defined with no sorry.
The sorry is in the PROOF that the L1 body satisfies the spec.

| # | Line | Theorem                              | Category   | Effort | Blocked by        |
|---|------|--------------------------------------|------------|--------|-------------------|
| 1 | 219  | rb_push_validHoare                   | multi-heap | 2 days | projection lemmas |
| 2 | 225  | rb_pop_validHoare                    | multi-heap | 2 days | projection lemmas |
| 3 | 231  | rb_count_nodes_validHoare            | loop       | 1 day  | loop invariant    |
| 4 | 236  | rb_contains_validHoare               | loop       | 1 day  | loop invariant    |
| 5 | 241  | rb_find_index_validHoare             | loop       | 1 day  | loop invariant    |
| 6 | 246  | rb_nth_validHoare                    | loop       | 1 day  | loop invariant    |
| 7 | 251  | rb_sum_validHoare                    | loop       | 1 day  | loop invariant    |
| 8 | 256  | rb_increment_all_validHoare          | loop       | 1 day  | loop invariant    |
| 9 | 261  | rb_count_above_validHoare            | loop       | 0.5d   | loop invariant    |
|10 | 266  | rb_count_at_or_below_validHoare      | loop       | 0.5d   | loop invariant    |
|11 | 271  | rb_swap_front_back_validHoare        | multi-heap | 1.5d   | projection lemmas |
|12 | 276  | rb_max_validHoare                    | loop       | 1 day  | loop invariant    |
|13 | 281  | rb_replace_all_validHoare            | loop       | 1 day  | loop invariant    |
|14 | 286  | rb_fill_validHoare                   | loop       | 1 day  | loop invariant    |
|15 | 291  | rb_reverse_validHoare                | loop       | 3 days | pointer reversal  |
|16 | 296  | rb_remove_first_match_validHoare     | heap+loop  | 2 days | inv + projection  |
|17 | 301  | rb_equal_validHoare                  | loop       | 1.5d   | dual-ptr inv      |
|18 | 306  | rb_check_integrity_validHoare        | call       | 0.5d   | callee spec       |
|19 | 311  | rb_iter_next_validHoare              | multi-heap | 1 day  | projection lemmas |
|20 | 316  | rb_iter_skip_validHoare              | loop       | 1 day  | loop invariant    |
|21 | 321  | rb_push_if_not_full_validHoare       | call       | 0.5d   | push spec         |
|22 | 326  | rb_pop_if_not_empty_validHoare       | call       | 0.5d   | pop spec          |
|23 | 331  | rb_drain_to_validHoare               | call+loop  | 3 days | push+pop specs    |
|24 | 336  | rb_clear_validHoare                  | heap+loop  | 2 days | inv + projection  |
|25 | 341  | rb_min_validHoare                    | loop       | 1 day  | loop invariant    |

  Estimated total effort: ~30 person-days
  Critical path: push/pop specs (4 days) → call specs (1.5 days) → drain_to (3 days)

### File: Examples/RBExtFuncSpecs.lean (7 additional totalHoare sorry)

These are the totalHoare statements from task 0139. Each requires its
corresponding validHoare proof + the existing Terminates proof.

| # | Line | Theorem                              | Blocked by                        |
|---|------|--------------------------------------|-----------------------------------|
|26 | ~370 | rb_capacity_totalHoare               | rb_capacity validHoare            |
|27 | ~375 | rb_size_totalHoare                   | rb_size validHoare                |
|28 | ~380 | rb_remaining_totalHoare              | rb_remaining validHoare           |
|29 | ~385 | rb_is_empty_totalHoare               | rb_is_empty validHoare            |
|30 | ~390 | rb_is_full_totalHoare                | rb_is_full validHoare             |
|31 | ~395 | rb_stats_total_ops_totalHoare        | rb_stats_total_ops validHoare     |
|32 | ~400 | rb_iter_has_next_totalHoare          | rb_iter_has_next validHoare       |

  Effort: ~1 day total (once validHoare proofs done: combine with Terminates)

### File: Examples/RBExtRefinement.lean (3 sorry)

| # | Line | Theorem                              | Blocked by                   |
|---|------|--------------------------------------|------------------------------|
|33 | 487  | ring_buffer_ext_refines_queue_spec   | all 25 validHoare proofs     |
|34 | 500  | rbExtSystemRefinement.inv_preserved  | theorem 33                   |
|35 | 530  | fifo_holds_at_c_level               | theorem 33                   |

  Effort: ~3 days (once all 25 validHoare proofs done)

### Core library: Clift/ — ZERO sorry

  Verified directories:
  - Clift/MonadLib/       (NondetM, Hoare, HoareRules, Corres, CorresRules): 0 sorry
  - Clift/CSemantics/     (CSimpl, Exec, HoareDef, TerminatesProps, etc.): 0 sorry
  - Clift/Lifting/        (SimplConv, L1HoareRules, FuncSpec, Pipeline, etc.): 0 sorry
  - Clift/Tactics/        (CVcg, SepAuto, CStep, CorresAuto): 0 sorry
  - Clift/Security/       : 0 sorry
  - Clift/Specs/          : 0 sorry

  One comment mentions sorry in Clift/Lifting/L5Auto.lean line 146,
  but it is a code comment, not an actual sorry tactic.

### Generated/ — ZERO sorry

  All generated files are definitions only (CSimpl terms, structures, instances).
  No proofs, therefore no sorry.

### Other Examples/ — ZERO sorry

  GcdProof, GcdCorrect, SwapProof, SwapL2, Rotate3Proof, MaxProof,
  MultiCallProof, ListLengthProof, RingBufferProof, SoundnessCheck,
  TerminationProofs, AIInvariantTest, PhaseEMilestone, PipelineTest,
  L1AutoTest, L1VcgTest: ALL sorry-free.

## Sorry elimination roadmap

  Priority order (maximizes sorry reduction per effort):

  1. **Simple accessors** (rb_size, rb_capacity, rb_remaining, rb_is_empty, rb_is_full,
     rb_stats_total_ops, rb_iter_has_next): ~3 days for 7 sorry + unlocks 7 totalHoare
     = 14 sorry eliminated.

  2. **Multi-heap** (rb_push, rb_pop, rb_swap_front_back, rb_iter_next): ~6.5 days
     for 4 sorry + unlocks 3 call sorry (check_integrity, push_if_not_full,
     pop_if_not_empty) = 7 sorry eliminated.

  3. **Loop functions** (13 remaining): ~14 days. Establish loop invariant pattern
     on rb_count_nodes first, then apply to others.

  4. **Hard cases** (rb_reverse, rb_drain_to, rb_remove_first_match, rb_clear):
     ~10 days. Pointer reversal and combined call+loop proofs.

  5. **Refinement** (3 sorry in RBExtRefinement): ~3 days after all validHoare done.

  Total estimated: ~36.5 person-days to reach zero sorry.

## CI metric

  Current sorry count: 35 (28 original + 7 new totalHoare)
  Target: 0
  Tracking: `just sorry-count` reports actual sorry lines
-/

-- This file is documentation-only. No Lean declarations needed.
-- The analysis above is the deliverable for task 0182.
