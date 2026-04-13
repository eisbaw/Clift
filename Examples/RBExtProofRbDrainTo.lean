-- Proof for rb_drain_to_validHoare
-- Inter-procedural with loop: calls rb_pop AND rb_push via dynCom on each iteration.
-- Template: rb_push_if_not_full_validHoare, rb_check_integrity_validHoare
--
-- STATUS: Partially proven. The outer catch+skip structure, initial modify,
-- exit condition, and final modify+throw are fully proven.
-- The while loop body obligations require infrastructure not yet available:
--   1. A working rb_pop validHoare proof (RBPopProof.lean has build errors)
--   2. A frame rule for heapPtrValid across opaque callee calls
--   3. LinkedListValid maintenance for src.head across iterations
-- See detailed analysis in the sorry comments below.
import Examples.RBExtSpecs
import Examples.RBExtProofsLoops
set_option maxHeartbeats 51200000
set_option maxRecDepth 4096
open RingBufferExt

attribute [local irreducible] hVal heapUpdate heapPtrValid

-- Mark all l1 bodies irreducible to prevent kernel from unfolding callee bodies
attribute [local irreducible]
  l1_rb_init_body l1_rb_push_body l1_rb_pop_body l1_rb_peek_body
  l1_rb_size_body l1_rb_is_empty_body l1_rb_is_full_body l1_rb_clear_body
  l1_rb_count_nodes_body l1_rb_contains_body l1_rb_peek_back_body
  l1_rb_increment_all_body l1_rb_sum_body
  l1_rb_capacity_body l1_rb_remaining_body
  l1_rb_push_if_not_full_body l1_rb_pop_if_not_empty_body
  l1_rb_drain_to_body l1_rb_find_index_body l1_rb_nth_body
  l1_rb_remove_first_match_body l1_rb_stats_init_body
  l1_rb_stats_update_push_body l1_rb_stats_update_pop_body
  l1_rb_stats_reset_body l1_rb_stats_total_ops_body
  l1_rb_iter_init_body l1_rb_iter_has_next_body l1_rb_iter_next_body
  l1_rb_iter_skip_body l1_rb_equal_body l1_rb_swap_front_back_body
  l1_rb_min_body l1_rb_max_body l1_rb_replace_all_body
  l1_rb_reverse_body l1_rb_count_above_body l1_rb_count_at_or_below_body
  l1_rb_fill_body l1_rb_check_integrity_body

-- Key lemma: rb_pop only produces ok results (it's catch+skip)
private theorem rb_pop_results_ok (s : ProgramState) :
    ∀ r s', (r, s') ∈ (l1_rb_pop_body s).results → r = Except.ok () := by
  unfold l1_rb_pop_body; exact L1_catch_skip_ok_only _ s

-- Key lemma: rb_push only produces ok results (it's catch+skip)
private theorem rb_push_results_ok (s : ProgramState) :
    ∀ r s', (r, s') ∈ (l1_rb_push_body s).results → r = Except.ok () := by
  unfold l1_rb_push_body; exact L1_catch_skip_ok_only _ s

/-! ## Callee validHoare specs for drain_to

rb_push callee: delegates to rb_push_validHoare (from RBExtProofsLoops, builds successfully).
Postcondition: r = ok (structural from catch+skip).
-/

-- rb_push callee spec: ok-only postcondition via rb_push_validHoare.
private theorem rb_push_drain_hoare :
    validHoare
      (fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧
                heapPtrValid s.globals.rawHeap s.locals.node ∧
                (hVal s.globals.rawHeap s.locals.rb).count <
                  (hVal s.globals.rawHeap s.locals.rb).capacity ∧
                ((hVal s.globals.rawHeap s.locals.rb).tail ≠ Ptr.null →
                  heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).tail) ∧
                ((hVal s.globals.rawHeap s.locals.rb).tail ≠ Ptr.null →
                  ptrDisjoint s.locals.node (hVal s.globals.rawHeap s.locals.rb).tail))
      l1_rb_push_body
      (fun r _ => r = Except.ok ()) := by
  intro s hpre
  have ⟨h_nf, _⟩ := rb_push_validHoare s hpre
  exact ⟨h_nf, fun r s' h_mem => rb_push_results_ok s r s' h_mem⟩

/-! ## Loop invariant

The invariant tracks heapPtrValid for the four key pointers (src, dst, scratch, temp_node)
and the callee preconditions for head/tail validity.
-/

private abbrev drainInv (s : ProgramState) : Prop :=
  heapPtrValid s.globals.rawHeap s.locals.src ∧
  heapPtrValid s.globals.rawHeap s.locals.dst ∧
  heapPtrValid s.globals.rawHeap s.locals.scratch ∧
  heapPtrValid s.globals.rawHeap s.locals.temp_node ∧
  ((hVal s.globals.rawHeap s.locals.src).head ≠ Ptr.null →
    heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.src).head) ∧
  ((hVal s.globals.rawHeap s.locals.dst).tail ≠ Ptr.null →
    heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.dst).tail)

/-! ## Main proof

Structure: catch(seq(modify(transferred:=0), seq(while(cond, body), modify(ret)+throw)), skip)
Outer catch+skip makes all results ok. Postcondition: heapPtrValid src ∧ dst.

BLOCKERS (4 items, causing the sorry):

1. **rb_pop callee spec**: RBPopProof.lean and RBExtProofRbPop.lean have build errors
   (kernel deep recursion, application type mismatch, simp failures). Without a working
   rb_pop validHoare, we cannot prove the dynCom(pop) step doesn't fail.
   FIX: Repair the rb_pop proof files. The proof structure is sound (split into 3 parts
   with opaque Locals setters), but needs fixing at lines 79, 128.

2. **Frame rule for heapPtrValid**: After a dynCom(rb_pop) call, we know
   heapPtrValid for src (from callee postcondition) but NOT for dst, scratch, or temp_node.
   The callee spec doesn't include these. heapUpdate_preserves_heapPtrValid guarantees
   preservation, but we can't prove this for opaque callee bodies.
   FIX: Either (a) add a general "L1 programs preserve heapPtrValid for all initially-valid
   pointers" theorem (true by construction since L1 only modifies heap via heapUpdate),
   or (b) strengthen callee postconditions to include all needed pointer validity.

3. **LinkedListValid maintenance**: After rb_pop advances src's head to head->next,
   we need heapPtrValid for the new head. This requires LinkedListValid or WellFormedList
   for the src buffer's linked list, maintained across iterations.
   FIX: Add WellFormedList src.head to the precondition, prove it's maintained by rb_pop.

4. **ptrDisjoint for rb_push**: rb_push requires ptrDisjoint(node, dst.tail). After the
   first push, dst.tail = temp_node = node, so ptrDisjoint fails on subsequent iterations.
   FIX: Either weaken rb_push's precondition (ptrDisjoint is only needed for the
   postcondition, not for non-failure), or strengthen rb_drain_to's precondition with
   sufficient disjointness conditions.
-/

theorem rb_drain_to_validHoare :
    rb_drain_to_spec.satisfiedBy RingBufferExt.l1_rb_drain_to_body := by
  unfold FuncSpec.satisfiedBy rb_drain_to_spec l1_rb_drain_to_body
  -- Structure: catch(seq(modify(transferred:=0), seq(while(...), modify+throw)), skip)
  apply L1_hoare_catch (R := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.src ∧
    heapPtrValid s.globals.rawHeap s.locals.dst)
  · -- CATCH BODY: seq(modify(transferred:=0), seq(while, modify+throw))
    apply L1_hoare_seq (R := drainInv)
    · -- MODIFY: transferred := 0. Preserves all invariant fields (locals only change).
      intro s ⟨h_src, h_dst, h_scratch, h_temp, h_head, h_tail⟩
      constructor
      · intro hf; exact hf  -- modify doesn't fail
      · intro r s' h_mem
        have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
        exact ⟨h_src, h_dst, h_scratch, h_temp, h_head, h_tail⟩
    · -- SEQ: seq(while, modify+throw)
      apply L1_hoare_seq (R := fun s =>
        heapPtrValid s.globals.rawHeap s.locals.src ∧
        heapPtrValid s.globals.rawHeap s.locals.dst)
      · -- WHILE: while(transferred < max_drain, LOOP_BODY)
        apply L1_hoare_while (I := drainInv)
        · -- h_init: drainInv → drainInv (identity)
          intro s h; exact h
        · -- h_body_nf: drainInv ∧ cond true → body doesn't fail
          -- BLOCKED: requires callee non-failure for both rb_pop and rb_push.
          -- rb_pop: needs working rb_pop proof (BLOCKER 1)
          -- rb_push: needs rb_push_drain_hoare + correct setup preconditions
          -- Frame rule needed to propagate heapPtrValid (BLOCKER 2)
          intro s _h_inv _hcond
          sorry
        · -- h_body_inv: drainInv preserved on ok return
          -- BLOCKED: requires tracking src.head and dst.tail through dynCom calls.
          -- src.head after rb_pop: new head = old_head.next. Need LinkedListValid (BLOCKER 3).
          -- dst.tail after rb_push: new tail = temp_node. heapPtrValid temp_node preserved.
          -- But need frame rule to know temp_node stays valid (BLOCKER 2).
          -- ptrDisjoint for rb_push on 2nd+ iteration (BLOCKER 4).
          intro _s _s' _h_inv _hcond _h_ok
          sorry
        · -- h_exit: drainInv ∧ cond false → while Q ok
          -- FULLY PROVEN: extract heapPtrValid src ∧ dst from invariant.
          intro s ⟨h_src, h_dst, _, _, _, _⟩ _
          exact ⟨h_src, h_dst⟩
        · -- h_abrupt: body error → while Q error (heapPtrValid src ∧ dst)
          -- BLOCKED: same as h_body_nf (needs frame rule to show heapPtrValid
          -- preserved at every throw point through callee calls).
          intro _s _s' _h_inv _hcond _h_err
          sorry
      · -- MODIFY+THROW after while: produce error with R = heapPtrValid src ∧ dst
        -- FULLY PROVEN: modify(ret:=transferred) only changes locals, heapPtrValid preserved.
        intro s ⟨h_src, h_dst⟩
        have h := L1_modify_throw_result
          (fun s : ProgramState => { s with locals := { s.locals with ret__val := s.locals.transferred } }) s
        exact ⟨h.2, fun r s' h_mem => by
          rw [h.1] at h_mem; have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
          exact ⟨h_src, h_dst⟩⟩
  · -- HANDLER (skip): from R, establish postcondition
    -- FULLY PROVEN: skip preserves state, R directly gives postcondition.
    intro s ⟨h_src, h_dst⟩
    exact ⟨not_false, fun r s' h_mem => by
      have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
      intro _; exact ⟨h_src, h_dst⟩⟩
