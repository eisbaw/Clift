-- Task 0182: Sorry audit — systematic inventory of all sorry in the codebase
--
-- For each sorry: file, line, what it proves, why it's sorry, what's needed
-- to fix it, estimated effort.
--
-- A formal methods reviewer will grep for sorry FIRST. This file is the
-- honest accounting that demonstrates we know exactly where the gaps are.

import Clift.CSemantics

/-! # Sorry Audit — 2026-04-14

## Executive summary

  Total sorry in codebase: 17
  - Core library (Clift/):           0  (ZERO sorry in MonadLib, CSemantics, Lifting, Tactics)
  - Generated code:                  0  (ZERO sorry in Generated/)
  - Examples/PriorityQueueProof:     5  (pq_swap body, bubble_up, insert guards, extract_min)
  - Examples/RBExtProofRbDrainTo:    5  (drain_to loop: non-failure, invariant, abrupt + callee chains)
  - Examples/RBExtProofsLoops:       2  (count_nodes, sum — tautological postconditions)
  - Examples/RBExtProofsLoops2:      2  (count_above, count_at_or_below — tautological postconditions)
  - Examples/RBExtRefinement:        3  (refinement: all-ops, inv_preserved, fifo transfer)
  - Other Examples:                  0  (ZERO sorry in GCD, Swap, SoundnessCheck, etc.)

  The 17 sorry are ALL in the Examples/ directory, not in the core library.
  The core library (MonadLib, CSemantics, Lifting, Tactics) is sorry-free.

## Severity classification

  - **Core sorry** (would invalidate the framework): 0
  - **Proof sorry — tautological postcondition** (need spec strengthening): 4
    (count_nodes, sum, count_above, count_at_or_below — blocked on TASK-0231)
  - **Proof sorry — inter-procedural** (need dynCom/call composition): 8
    (pq_swap body, bubble_up, insert x2, extract_min, drain_to x3)
  - **Blocked sorry** (transitively blocked on validHoare proofs): 3
    (RBExtRefinement: all-ops, inv_preserved, fifo)
  - **Stub sorry** (placeholder for future work): 0

## Detailed inventory

### File: Examples/PriorityQueueProof.lean (5 sorry)

Priority queue proofs involving array-based heap operations with dynCom calls.

| # | Line | Theorem / context                    | Category       | Effort | Blocked by                   |
|---|------|--------------------------------------|----------------|--------|------------------------------|
| 1 | 363  | pq_swap body (catch body)            | guard+heap     | 1 day  | heapUpdate chain reasoning   |
| 2 | 395  | pq_bubble_up_ok_hoare                | while+dynCom   | 3 days | loop inv + dynCom(pq_swap)   |
| 3 | 449  | pq_insert (guard+modify data write)  | guard+heap     | 0.5d   | dataArrayValid preservation  |
| 4 | 455  | pq_insert (dynCom+size++ chain)      | dynCom+chain   | 1 day  | bubble_up callee spec        |
| 5 | 466  | pq_extract_min_correct               | call+loop      | 3 days | bubble_down callee spec      |

  Estimated effort: ~8.5 person-days
  Critical path: pq_swap (1d) -> bubble_up (3d) -> insert/extract_min (4d)

### File: Examples/RBExtProofRbDrainTo.lean (5 sorry)

Ring buffer drain-to: loop calling rb_pop on src and rb_push on dst via dynCom.

| # | Line | Theorem / context                    | Category       | Effort | Blocked by                   |
|---|------|--------------------------------------|----------------|--------|------------------------------|
| 6 | 148  | rb_pop_for_drain (not-empty branch)  | guard chain    | 1 day  | heapPtrValid chain           |
| 7 | 178  | rb_push_for_drain (not-full branch)  | guard chain    | 1 day  | heapPtrValid chain           |
| 8 | 239  | drain_to while h_body_nf             | dynCom+loop    | 2 days | callee non-failure           |
| 9 | 246  | drain_to while h_body_inv            | dynCom+loop    | 3 days | LinkedListValid in invariant |
|10 | 254  | drain_to while h_abrupt              | dynCom+loop    | 1 day  | heapUpdate preservation      |

  Estimated effort: ~8 person-days
  Critical path: pop/push callees (2d) -> loop body (5d)
  Blocker: invariant needs LinkedListValid for head-validity after iteration.

### File: Examples/RBExtProofsLoops.lean (2 sorry)

Loop proofs with tautological postconditions (count=count). Previous proofs
used validHoare_weaken_trivial_post and were moved to bogus/.

| # | Line | Theorem                              | Category       | Effort | Blocked by                   |
|---|------|--------------------------------------|----------------|--------|------------------------------|
|11 | 383  | rb_count_nodes_validHoare            | tautological   | 1 day  | TASK-0231 spec strengthening |
|12 |1452  | rb_sum_validHoare                    | tautological   | 1 day  | TASK-0231 spec strengthening |

  Estimated effort: ~2 person-days (after specs are strengthened)

### File: Examples/RBExtProofsLoops2.lean (2 sorry)

Same tautological postcondition issue as above. Split into separate file.

| # | Line | Theorem                              | Category       | Effort | Blocked by                   |
|---|------|--------------------------------------|----------------|--------|------------------------------|
|13 | 10   | rb_count_above_validHoare            | tautological   | 0.5d   | TASK-0231 spec strengthening |
|14 | 14   | rb_count_at_or_below_validHoare      | tautological   | 0.5d   | TASK-0231 spec strengthening |

  Estimated effort: ~1 person-day (after specs are strengthened)

### File: Examples/RBExtRefinement.lean (3 sorry)

| # | Line | Theorem                              | Category       | Effort | Blocked by                   |
|---|------|--------------------------------------|----------------|--------|------------------------------|
|15 | 507  | ring_buffer_ext_refines_queue_spec   | refinement     | 3 days | all validHoare proofs        |
|16 | 520  | rbExtSystemRefinement.inv_preserved  | refinement     | 1 day  | theorem 15                   |
|17 | 550  | fifo_holds_at_c_level               | refinement     | 1 day  | theorem 15                   |

  Estimated effort: ~5 person-days (once all validHoare proofs done)

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
  L1AutoTest, L1VcgTest, RBExtProofsSimple, RBExtProofsLoops (proven theorems),
  PacketParserProof, DmaBufferProof, Sel4CapProof: ALL sorry-free.

## Sorry elimination roadmap

  Priority order (maximizes sorry reduction per effort):

  1. **Tautological specs** (TASK-0231): Strengthen postconditions for
     count_nodes, sum, count_above, count_at_or_below. Once specs are
     meaningful, reproving is ~3 person-days for 4 sorry eliminated.

  2. **Guard chains** (drain_to callees): rb_pop_for_drain and rb_push_for_drain
     are Pattern C (multi-step guard+modify). ~2 days for 2 sorry eliminated.

  3. **PQ accessors** (pq_swap body, insert guard+modify): Pattern C guard
     chains with heap reasoning. ~1.5 days for 2 sorry eliminated.

  4. **Inter-procedural** (bubble_up, insert dynCom chain, extract_min,
     drain_to loop): These need dynCom/call composition (Pattern E).
     Currently BLOCKED on L1_hoare_dynCom_call rule (TASK-0235).
     ~12 days for 6 sorry once the rule exists.

  5. **Refinement** (3 sorry in RBExtRefinement): ~5 days after all
     validHoare proofs done. Transitively blocked on everything above.

  Total estimated: ~23.5 person-days to reach zero sorry.
  Hard blocker: TASK-0235 (dynCom call rule) blocks 6 sorry.

## CI metric

  Current sorry count: 17
  Target: 0
  Tracking: `just sorry-count` and `python3 tools/lint/audit.py --skip-lake`
-/

-- This file is documentation-only. No Lean declarations needed.
-- The analysis above is the deliverable for task 0182.
