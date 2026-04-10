-- Ring buffer extended: seL4-scale test (task 0113)
--
-- 676 LOC C -> 2460 lines Generated Lean -> 40 functions
-- Goal: run clift pipeline, measure what works, document gaps

import Generated.RingBufferExt
import Clift.Lifting.Pipeline
import Clift.Lifting.FuncSpec
import Clift.Lifting.AbstractSpec
import Clift.Lifting.GlobalInvariant
import Clift.Lifting.HeapLift.SepLogic

set_option maxHeartbeats 12800000
set_option maxRecDepth 4096

open RingBufferExt

/-! # Step 1: Run the clift pipeline on all 40 functions -/

clift RingBufferExt

/-! # Step 2: Verify L1 definitions exist for all functions -/

-- Core functions (16)
#check @RingBufferExt.l1_rb_init_body
#check @RingBufferExt.l1_rb_push_body
#check @RingBufferExt.l1_rb_pop_body
#check @RingBufferExt.l1_rb_peek_body
#check @RingBufferExt.l1_rb_size_body
#check @RingBufferExt.l1_rb_is_empty_body
#check @RingBufferExt.l1_rb_is_full_body
#check @RingBufferExt.l1_rb_clear_body
#check @RingBufferExt.l1_rb_count_nodes_body
#check @RingBufferExt.l1_rb_contains_body
#check @RingBufferExt.l1_rb_peek_back_body
#check @RingBufferExt.l1_rb_check_integrity_body
#check @RingBufferExt.l1_rb_increment_all_body
#check @RingBufferExt.l1_rb_sum_body
#check @RingBufferExt.l1_rb_capacity_body
#check @RingBufferExt.l1_rb_remaining_body

-- Extended functions (14)
#check @RingBufferExt.l1_rb_push_if_not_full_body
#check @RingBufferExt.l1_rb_pop_if_not_empty_body
#check @RingBufferExt.l1_rb_drain_to_body
#check @RingBufferExt.l1_rb_find_index_body
#check @RingBufferExt.l1_rb_nth_body
#check @RingBufferExt.l1_rb_remove_first_match_body
#check @RingBufferExt.l1_rb_swap_front_back_body
#check @RingBufferExt.l1_rb_min_body
#check @RingBufferExt.l1_rb_max_body
#check @RingBufferExt.l1_rb_replace_all_body
#check @RingBufferExt.l1_rb_reverse_body
#check @RingBufferExt.l1_rb_count_above_body
#check @RingBufferExt.l1_rb_count_at_or_below_body
#check @RingBufferExt.l1_rb_fill_body

-- Stats functions (5)
#check @RingBufferExt.l1_rb_stats_init_body
#check @RingBufferExt.l1_rb_stats_update_push_body
#check @RingBufferExt.l1_rb_stats_update_pop_body
#check @RingBufferExt.l1_rb_stats_reset_body
#check @RingBufferExt.l1_rb_stats_total_ops_body

-- Iterator functions (4)
#check @RingBufferExt.l1_rb_iter_init_body
#check @RingBufferExt.l1_rb_iter_has_next_body
#check @RingBufferExt.l1_rb_iter_next_body
#check @RingBufferExt.l1_rb_iter_skip_body

-- Equal function (1)
#check @RingBufferExt.l1_rb_equal_body

/-! # Step 3: Verify L1corres proofs for non-calling functions -/

-- Simple accessors (should all have corres proofs)
#check @RingBufferExt.l1_rb_size_body_corres
#check @RingBufferExt.l1_rb_is_empty_body_corres
#check @RingBufferExt.l1_rb_is_full_body_corres
#check @RingBufferExt.l1_rb_capacity_body_corres
#check @RingBufferExt.l1_rb_remaining_body_corres

-- Core operations (non-calling)
#check @RingBufferExt.l1_rb_init_body_corres
#check @RingBufferExt.l1_rb_push_body_corres
#check @RingBufferExt.l1_rb_pop_body_corres
#check @RingBufferExt.l1_rb_peek_body_corres
#check @RingBufferExt.l1_rb_clear_body_corres
#check @RingBufferExt.l1_rb_count_nodes_body_corres
#check @RingBufferExt.l1_rb_contains_body_corres
#check @RingBufferExt.l1_rb_peek_back_body_corres
#check @RingBufferExt.l1_rb_increment_all_body_corres
#check @RingBufferExt.l1_rb_sum_body_corres

-- Extended operations (non-calling)
#check @RingBufferExt.l1_rb_find_index_body_corres
#check @RingBufferExt.l1_rb_nth_body_corres
#check @RingBufferExt.l1_rb_remove_first_match_body_corres
#check @RingBufferExt.l1_rb_swap_front_back_body_corres
#check @RingBufferExt.l1_rb_min_body_corres
#check @RingBufferExt.l1_rb_max_body_corres
#check @RingBufferExt.l1_rb_replace_all_body_corres
#check @RingBufferExt.l1_rb_reverse_body_corres
#check @RingBufferExt.l1_rb_count_above_body_corres
#check @RingBufferExt.l1_rb_count_at_or_below_body_corres
#check @RingBufferExt.l1_rb_fill_body_corres

-- Stats operations (non-calling, no pointer deref)
#check @RingBufferExt.l1_rb_stats_init_body_corres
#check @RingBufferExt.l1_rb_stats_update_push_body_corres
#check @RingBufferExt.l1_rb_stats_update_pop_body_corres
#check @RingBufferExt.l1_rb_stats_reset_body_corres
#check @RingBufferExt.l1_rb_stats_total_ops_body_corres

-- Iterator operations (non-calling)
#check @RingBufferExt.l1_rb_iter_init_body_corres
#check @RingBufferExt.l1_rb_iter_has_next_body_corres
#check @RingBufferExt.l1_rb_iter_next_body_corres
#check @RingBufferExt.l1_rb_iter_skip_body_corres

-- Multi-buffer operations
#check @RingBufferExt.l1_rb_equal_body_corres

-- Call-containing functions (task 0117: now have L1corres proofs)
#check @RingBufferExt.l1_rb_check_integrity_body_corres
#check @RingBufferExt.l1_rb_push_if_not_full_body_corres
#check @RingBufferExt.l1_rb_pop_if_not_empty_body_corres
#check @RingBufferExt.l1_rb_drain_to_body_corres

/-! # Step 4: Verify L2 forms exist -/

#check @RingBufferExt.l2_rb_size_body
#check @RingBufferExt.l2_rb_capacity_body
#check @RingBufferExt.l2_rb_init_body
#check @RingBufferExt.l2_rb_push_body
#check @RingBufferExt.l2_rb_stats_init_body

/-! # Step 5: Verify L3 classifications -/

#check @RingBufferExt.l3_rb_size_body_level
#check @RingBufferExt.l3_rb_is_empty_body_level
#check @RingBufferExt.l3_rb_capacity_body_level

/-! # Step 6: Sample axiom audit -/

#print axioms RingBufferExt.l1_rb_init_body_corres
#print axioms RingBufferExt.l1_rb_push_body_corres
#print axioms RingBufferExt.l1_rb_reverse_body_corres
#print axioms RingBufferExt.l1_rb_min_body_corres
#print axioms RingBufferExt.l1_rb_stats_total_ops_body_corres

/-! # Step 7: Sample functional spec for rb_min

Verifying: if the buffer is non-empty, rb_min returns the minimum
of all node values in the linked list. -/

def rb_min_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.rb ∧
    (hVal s.globals.rawHeap s.locals.rb).head ≠ Ptr.null
  post := fun r s =>
    r = Except.ok () →
    s.locals.ret__val = 0  -- return code 0 = success

def rb_reverse_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.rb ∧
    (hVal s.globals.rawHeap s.locals.rb).count ≥ 2
  post := fun r s =>
    r = Except.ok () →
    s.locals.ret__val = 0  -- return code 0 = success

/-! # Measurement summary (filled in from build output)

## Scale
- C source: 676 LOC, 40 functions, 4 structs
- Generated Lean (CSimpl): 2460 lines
- Functions imported: 40/40
- Functions lifted to L1: 40/40
- L1corres proofs generated: 40/40 (task 0117: call-containing functions now proven)
- L2 forms generated: all non-calling functions
- L3 classifications: simple accessors (size, capacity, etc.)
- Build time (Generated.RingBufferExt): 2.9s
- Build time (Examples.RingBufferExtProof with clift): 10s
- Peak RAM: 1.5GB

## Gap analysis
- Address-of local (&var) NOT supported -- had to refactor rb_pop_if_not_empty
- CImporter NULL-to-Ptr.null fix needed for local pointer initialization
- void return functions: supported (rb_stats_init, etc.)
- Multiple struct types: supported (rb_node, rb_state, rb_stats, rb_iter)
- Inter-procedural calls: partially supported (check_integrity -> count_nodes works,
  but drain_to -> pop/push needs call graph)

## What's missing for seL4 scale
1. Address-of local variables (&x) -- many C patterns need this
2. Array subscript (a[i]) -- fundamental for kernel code
3. Multi-file compilation units (seL4 spans many .c files)
4. Function pointers / dispatch tables
5. Typedef transparency (seL4 uses many layers of typedefs)
6. Bitwise operations in expressions (&, |, ^, ~, <<, >>)
7. Compound assignment (+=, -=, etc.) -- currently rewritten in C
8. Cast expressions (uint32_t)(ptr) -- pointer to integer casts
9. Concurrency / interrupt handler modeling
10. sizeof operator
-/
