-- rb_count_above and rb_count_at_or_below validHoare proofs
-- TASK-0231: Postconditions strengthened with ListCountAboveIs/ListCountAtOrBelowIs.
-- These proofs have conditionals (if value > threshold) in the loop body,
-- which makes the invariant proof more complex than rb_count_nodes/rb_sum.
--
-- Blocker for sorry elimination:
--   1. The loop body has L1.condition, requiring case analysis on the condition
--   2. ListCountAboveIs/ListCountAtOrBelowIs have 3 constructors (null, cons_above, cons_not_above)
--      and dependent pattern matching on them with fixed pointer indices triggers
--      Lean 4 kernel depth issues and dependent elimination failures
--   3. Need custom decomposition lemmas that avoid dependent elimination
--
-- The proof architecture is identical to rb_count_nodes_validHoare:
--   - Loop invariant: count + cnt_remaining = cnt_total
--   - Conditional: above case increments count (cnt_cur = m+1 → (count+1)+m = cnt_head)
--                  not-above case: skip (cnt_cur = m → count+m = cnt_head)
--   - Exit: cur = null → cnt_remaining = 0 → count = cnt_total
--   - Teardown: ret_val = count
import Examples.RBExtSpecs
open RingBufferExt

-- Postcondition is now strengthened (TASK-0231) — no longer tautological
-- Proof requires loop invariant with ListCountAboveIs witness
theorem rb_count_above_validHoare :
    rb_count_above_spec.satisfiedBy RingBufferExt.l1_rb_count_above_body := by
  sorry -- TASK-0231: needs loop invariant proof with conditional (L1.condition)
         -- See rb_count_nodes_validHoare in RBExtProofsLoops.lean for the pattern
         -- Additional complexity: cond (value > threshold) count++ skip in loop body

theorem rb_count_at_or_below_validHoare :
    rb_count_at_or_below_spec.satisfiedBy RingBufferExt.l1_rb_count_at_or_below_body := by
  sorry -- TASK-0231: same structure as rb_count_above with <= instead of >
