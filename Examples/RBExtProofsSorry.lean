-- Sorry (not yet proven) validHoare theorems for ring buffer functions.
-- Split from RBExtFuncSpecs.lean (task 0233).
--
-- 15 sorry remaining:
--   Multi-heap: rb_pop, rb_swap_front_back
--   Loop+mutation: rb_increment_all, rb_replace_all, rb_fill, rb_reverse,
--                  rb_remove_first_match, rb_clear
--   Dual-pointer loop: rb_equal
--   Inter-procedural: rb_check_integrity, rb_iter_next, rb_iter_skip,
--                     rb_push_if_not_full, rb_pop_if_not_empty, rb_drain_to

import Examples.RBExtSpecs

set_option maxHeartbeats 12800000
set_option maxRecDepth 4096

open RingBufferExt

theorem rb_pop_validHoare :
    rb_pop_spec.satisfiedBy RingBufferExt.l1_rb_pop_body := by
  sorry

theorem rb_increment_all_validHoare :
    rb_increment_all_spec.satisfiedBy RingBufferExt.l1_rb_increment_all_body := by
  sorry

-- rb_swap_front_back: multi-step heap mutation (3 checks + 3 writes)
-- SORRY: The 3 conditions are eliminable (L1_hoare_condition + precondition contradictions).
-- The guard+modify chain after conditions needs ptrDisjoint(head, rb) and ptrDisjoint(tail, rb)
-- to show hVal of rb is unchanged after heapUpdate to head/tail nodes.
-- Without these, the guard predicates at intermediate states cannot be discharged.
-- Fix: add ptrDisjoint assumptions to rb_swap_front_back_spec.pre.
theorem rb_swap_front_back_validHoare :
    rb_swap_front_back_spec.satisfiedBy RingBufferExt.l1_rb_swap_front_back_body := by
  sorry

-- rb_replace_all: loop with conditional heap mutation
theorem rb_replace_all_validHoare :
    rb_replace_all_spec.satisfiedBy RingBufferExt.l1_rb_replace_all_body := by
  sorry

-- rb_fill: loop with heap mutation per iteration
theorem rb_fill_validHoare :
    rb_fill_spec.satisfiedBy RingBufferExt.l1_rb_fill_body := by
  sorry

-- rb_reverse: loop with pointer reversal (hardest loop proof)
theorem rb_reverse_validHoare :
    rb_reverse_spec.satisfiedBy RingBufferExt.l1_rb_reverse_body := by
  sorry

-- rb_remove_first_match: loop with conditional node removal
theorem rb_remove_first_match_validHoare :
    rb_remove_first_match_spec.satisfiedBy RingBufferExt.l1_rb_remove_first_match_body := by
  sorry

-- rb_equal: dual-pointer loop
theorem rb_equal_validHoare :
    rb_equal_spec.satisfiedBy RingBufferExt.l1_rb_equal_body := by
  sorry

-- rb_check_integrity: calls rb_count_nodes
-- The postcondition is tautological: (ret=0 ∨ ret=1) ∧ (count = count).
-- Every exit path sets ret to 0 or 1.
-- The dynCom+call to rb_count_nodes is handled via L1_hoare_dynCom.
-- Explore L1 body structure
private theorem check_integrity_body_eq :
    RingBufferExt.l1_rb_check_integrity_body =
    L1.catch
      (L1.seq
        (L1.dynCom (fun saved : ProgramState =>
          L1.seq (L1.modify (fun s => { s with locals := { s.locals with rb := s.locals.rb } }))
                 (L1.seq (L1.call RingBufferExt.l1ProcEnv "rb_count_nodes")
                         (L1.modify (fun s => { s with locals := { saved.locals with actual := s.locals.ret__val } })))))
        (L1.seq
          (L1.condition (fun s => decide (s.locals.actual ≠ (hVal s.globals.rawHeap s.locals.rb).count))
            (L1.seq (L1.modify (fun s => { s with locals := { s.locals with ret__val := 0 } })) L1.throw)
            L1.skip)
          (L1.seq
            (L1.condition (fun s => decide ((hVal s.globals.rawHeap s.locals.rb).count = 0))
              (L1.seq
                (L1.condition (fun s => decide ((hVal s.globals.rawHeap s.locals.rb).head ≠ Ptr.null))
                  (L1.seq (L1.modify (fun s => { s with locals := { s.locals with ret__val := 0 } })) L1.throw)
                  L1.skip)
                (L1.condition (fun s => decide ((hVal s.globals.rawHeap s.locals.rb).tail ≠ Ptr.null))
                  (L1.seq (L1.modify (fun s => { s with locals := { s.locals with ret__val := 0 } })) L1.throw)
                  L1.skip))
              L1.skip)
            (L1.seq
              (L1.condition (fun s => decide ((hVal s.globals.rawHeap s.locals.rb).count ≠ 0))
                (L1.seq
                  (L1.condition (fun s => decide ((hVal s.globals.rawHeap s.locals.rb).head = Ptr.null))
                    (L1.seq (L1.modify (fun s => { s with locals := { s.locals with ret__val := 0 } })) L1.throw)
                    L1.skip)
                  (L1.condition (fun s => decide ((hVal s.globals.rawHeap s.locals.rb).tail = Ptr.null))
                    (L1.seq (L1.modify (fun s => { s with locals := { s.locals with ret__val := 0 } })) L1.throw)
                    L1.skip))
                L1.skip)
              (L1.seq (L1.modify (fun s => { s with locals := { s.locals with ret__val := 1 } })) L1.throw)))))
      L1.skip := by
  unfold RingBufferExt.l1_rb_check_integrity_body
  rfl

-- rb_check_integrity: calls rb_count_nodes
theorem rb_check_integrity_validHoare :
    rb_check_integrity_spec.satisfiedBy RingBufferExt.l1_rb_check_integrity_body := by
  sorry

-- rb_iter_next: multi-step heap (conditional + guard+modify chain)
-- Structure: catch(seq(cond(null→ret1+throw,skip), guard_chain+ret0+throw), skip)
-- Both paths set ret to 0 or 1 and throw, caught by skip.
-- Type disjointness: UInt32(tag 1) vs C_rb_iter(tag 203) vs C_rb_node(tag 200).

private theorem C_UInt32_iter_typeTag_ne :
    @CType.typeTag UInt32 _ ≠ @CType.typeTag C_rb_iter _ := by decide

private theorem C_iter_node_typeTag_ne :
    @CType.typeTag C_rb_iter _ ≠ @CType.typeTag C_rb_node _ := by decide

private theorem out_val_iter_disjoint {h : HeapRawState} {p : Ptr UInt32} {q : Ptr C_rb_iter}
    (hp : heapPtrValid h p) (hq : heapPtrValid h q) :
    ptrDisjoint p q :=
  heapPtrValid_different_type_disjoint hp hq C_UInt32_iter_typeTag_ne

set_option maxRecDepth 8192 in
set_option maxHeartbeats 51200000 in
theorem rb_iter_next_validHoare :
    rb_iter_next_spec.satisfiedBy RingBufferExt.l1_rb_iter_next_body := by
  unfold FuncSpec.satisfiedBy rb_iter_next_spec
  -- Abbreviate the catch-level error state predicate
  let CatchR := fun s : ProgramState =>
    (s.locals.ret__val = 0 ∨ s.locals.ret__val = 1) ∧
    heapPtrValid s.globals.rawHeap s.locals.iter
  -- Structure: L1.catch body L1.skip. Both branches throw → caught by skip.
  apply L1_hoare_catch (R := CatchR)
  · -- Body: seq(cond(null check), rest_chain)
    -- After cond: non-null path continues; null path throws (error→R).
    let IntermR := fun s : ProgramState =>
      heapPtrValid s.globals.rawHeap s.locals.iter ∧
      heapPtrValid s.globals.rawHeap s.locals.out_val ∧
      (hVal s.globals.rawHeap s.locals.iter).current ≠ Ptr.null ∧
      heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.iter).current
    apply L1_hoare_seq (R := IntermR)
    · -- cond(current==null, modify(ret:=1)+throw, skip)
      apply L1_hoare_condition
      · -- True: current==null → seq(modify ret:=1, throw)
        apply L1_hoare_modify_throw_catch
          (Q_ok := IntermR)
          (R := CatchR)
        intro s ⟨⟨hiter, _, _⟩, _⟩
        dsimp only [CatchR]
        exact ⟨Or.inr rfl, hiter⟩
      · -- False: current≠null → skip (preserves pre, ok result)
        intro s₀ ⟨⟨hiter, hout, hcur_impl⟩, hcond⟩
        simp only [decide_eq_false_iff_not] at hcond
        constructor
        · intro hf; exact hf
        · intro r s₁ hmem
          have ⟨hr, hs⟩ := Prod.mk.inj hmem; subst hr; subst hs
          exact ⟨hiter, hout, hcond, hcur_impl hcond⟩
    · -- rest: seq(guard+guard+modify, seq(guard+guard+modify, seq(cond, seq(modify, throw))))
      -- Step 1: guard(out_val) >> guard(current) >> modify(*out_val := current->value)
      apply L1_hoare_seq_ok (R := IntermR)
      · -- Decompose two different guards: guard(out_val) then guard(current)+modify
        apply L1_hoare_seq_ok (R := IntermR)
        · apply L1_hoare_pre (P := fun s =>
            heapPtrValid s.globals.rawHeap s.locals.out_val ∧ IntermR s)
          · intro s h; exact ⟨h.2.1, h⟩
          · exact L1_hoare_guard' _ _
        · apply L1_hoare_guard_modify_fused
          · intro s h; exact h.2.2.2
          · intro s ⟨hiter, hout, hne, hcur⟩
            dsimp only
            constructor; · rfl
            have hbo := heapPtrValid_bound hout
            have hbi := heapPtrValid_bound hiter
            have h_disj := out_val_iter_disjoint hout hiter
            exact ⟨heapUpdate_preserves_heapPtrValid _ _ _ _ hiter,
                   heapUpdate_preserves_heapPtrValid _ _ _ _ hout,
                   by rw [hVal_heapUpdate_disjoint _ _ _ _ hbo hbi h_disj]; exact hne,
                   by rw [hVal_heapUpdate_disjoint _ _ _ _ hbo hbi h_disj];
                      exact heapUpdate_preserves_heapPtrValid _ _ _ _ hcur⟩
      · -- Step 2: guard(iter) >> guard(current) >> modify(iter.current := current->next)
        let PostAdv := fun s : ProgramState =>
          heapPtrValid s.globals.rawHeap s.locals.iter ∧
          heapPtrValid s.globals.rawHeap s.locals.out_val
        apply L1_hoare_seq_ok (R := PostAdv)
        · -- Decompose two different guards
          apply L1_hoare_seq_ok (R := IntermR)
          · apply L1_hoare_pre (P := fun s =>
              heapPtrValid s.globals.rawHeap s.locals.iter ∧ IntermR s)
            · intro s h; exact ⟨h.1, h⟩
            · exact L1_hoare_guard' _ _
          · apply L1_hoare_guard_modify_fused
            · intro s h; exact h.2.2.2
            · intro s ⟨hiter, hout, _, _⟩
              dsimp only
              constructor; · rfl
              show PostAdv _
              exact ⟨heapUpdate_preserves_heapPtrValid _ _ _ _ hiter,
                     heapUpdate_preserves_heapPtrValid _ _ _ _ hout⟩
        · -- Step 3: seq(cond(remaining>0, guard(iter)+guard(iter)+modify(dec), skip), seq(modify(ret:=0), throw))
          apply L1_hoare_seq (R := PostAdv)
          · apply L1_hoare_condition
            · -- True: remaining>0 → guard(iter)>>guard(iter)>>modify(remaining-=1)
              apply L1_hoare_guard_guard_modify_fused
              · intro s ⟨h, _⟩; exact h.1
              · intro s ⟨⟨hiter, hout⟩, _⟩
                dsimp only
                show PostAdv _
                exact ⟨heapUpdate_preserves_heapPtrValid _ _ _ _ hiter,
                       heapUpdate_preserves_heapPtrValid _ _ _ _ hout⟩
            · -- False: skip
              intro s₀ ⟨⟨hiter, hout⟩, _⟩
              constructor
              · intro hf; exact hf
              · intro r s₁ hmem
                have ⟨hr, hs⟩ := Prod.mk.inj hmem; subst hr; subst hs
                exact ⟨hiter, hout⟩
          · -- seq(modify(ret:=0), throw)
            apply L1_hoare_modify_throw_catch (R := CatchR)
            intro s ⟨hiter, _⟩
            dsimp only [CatchR]
            exact ⟨Or.inl rfl, hiter⟩
  · -- Handler: skip. R s → Q (ok ()) s
    intro s ⟨hret, hiter⟩
    constructor
    · intro hf; exact hf
    · intro r s' hmem
      have ⟨hr, hs⟩ := Prod.mk.inj hmem; subst hr; subst hs
      intro _; exact ⟨hret, hiter⟩

-- rb_iter_skip: loop with heap mutation
theorem rb_iter_skip_validHoare :
    rb_iter_skip_spec.satisfiedBy RingBufferExt.l1_rb_iter_skip_body := by
  sorry

-- rb_push_if_not_full: calls rb_push
theorem rb_push_if_not_full_validHoare :
    rb_push_if_not_full_spec.satisfiedBy RingBufferExt.l1_rb_push_if_not_full_body := by
  sorry

-- rb_pop_if_not_empty: calls rb_pop
theorem rb_pop_if_not_empty_validHoare :
    rb_pop_if_not_empty_spec.satisfiedBy RingBufferExt.l1_rb_pop_if_not_empty_body := by
  sorry

-- rb_drain_to: loop + calls rb_pop + calls rb_push (hardest)
theorem rb_drain_to_validHoare :
    rb_drain_to_spec.satisfiedBy RingBufferExt.l1_rb_drain_to_body := by
  sorry

-- rb_clear: loop with heap mutation (existing spec in RingBufferExtProof.lean)
theorem rb_clear_validHoare :
    rb_clear_spec.satisfiedBy RingBufferExt.l1_rb_clear_body := by
  sorry
