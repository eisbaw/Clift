-- 13 sorry remaining (rb_pop + rb_iter_next proved)
import Examples.RBExtSpecs
set_option maxHeartbeats 12800000
set_option maxRecDepth 4096
open RingBufferExt

section RbPopProof
private abbrev pop3v (s : ProgramState) : Prop :=
  heapPtrValid s.globals.rawHeap s.locals.rb ∧ heapPtrValid s.globals.rawHeap s.locals.out_val ∧ heapPtrValid s.globals.rawHeap s.locals.front
@[irreducible] private def setRetVal₂ (s : ProgramState) (v : UInt32) : ProgramState :=
  { s with locals := { s.locals with ret__val := v } }
@[simp] private theorem setRetVal₂_globals (s v) : (setRetVal₂ s v).globals = s.globals := by unfold setRetVal₂; rfl
@[simp] private theorem setRetVal₂_retval (s v) : (setRetVal₂ s v).locals.ret__val = v := by unfold setRetVal₂; rfl
@[simp] private theorem setRetVal₂_outval (s v) : (setRetVal₂ s v).locals.out_val = s.locals.out_val := by unfold setRetVal₂; rfl
attribute [local irreducible] hVal heapUpdate

-- Part 1: steps 4-7 (the tail: cond+guard+guard+guard+modify+modify+throw)
set_option maxRecDepth 4096 in
set_option maxHeartbeats 25600000 in
private theorem rb_pop_part1 (m : L1Monad ProgramState) (Q : Except Unit Unit → ProgramState → Prop)
    (hm : m = L1.seq (L1.condition (fun s => decide ((hVal s.globals.rawHeap s.locals.rb).head = @Ptr.null C_rb_node)) (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.rb)) (L1.modify (fun s => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.rb ({ hVal s.globals.rawHeap s.locals.rb with tail := @Ptr.null C_rb_node }) } }))) L1.skip) (L1.seq (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.rb)) (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.rb)) (L1.modify (fun s => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.rb ({ hVal s.globals.rawHeap s.locals.rb with count := (hVal s.globals.rawHeap s.locals.rb).count - 1 }) } })))) (L1.seq (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.front)) (L1.modify (fun s => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.front ({ hVal s.globals.rawHeap s.locals.front with next := @Ptr.null C_rb_node }) } }))) (L1.seq (L1.modify (fun s => setRetVal₂ s 0)) L1.throw))))
    (hQ : ∀ s, s.locals.ret__val = 0 → heapPtrValid s.globals.rawHeap s.locals.out_val → Q (Except.error ()) s) :
    validHoare pop3v m Q := by
  subst hm
  unfold pop3v
  apply L1_hoare_seq_ok (R := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧ heapPtrValid s.globals.rawHeap s.locals.out_val ∧ heapPtrValid s.globals.rawHeap s.locals.front)
  · -- cond(head==null → guard+modify(tail:=null), skip)
    apply L1_hoare_condition'
    · apply L1_hoare_pre (P := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧ heapPtrValid s.globals.rawHeap s.locals.out_val ∧ heapPtrValid s.globals.rawHeap s.locals.front)
      · intro s ⟨hpre, _⟩
        exact hpre
      · apply L1_hoare_guard_modify_fused
        · intro s ⟨hrb, _, _⟩
          exact hrb
        · intro s ⟨hrb, hov, hfront⟩
          dsimp only
          exact ⟨rfl, heapUpdate_preserves_heapPtrValid _ _ _ _ hrb, heapUpdate_preserves_heapPtrValid _ _ _ _ hov, heapUpdate_preserves_heapPtrValid _ _ _ _ hfront⟩
    · apply L1_hoare_pre (P := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧ heapPtrValid s.globals.rawHeap s.locals.out_val ∧ heapPtrValid s.globals.rawHeap s.locals.front)
      · intro s ⟨hpre, _⟩
        exact hpre
      · intro s hR
        exact ⟨fun hf => hf, fun r s' hmem => let ⟨hr, hs⟩ := Prod.mk.inj hmem; hr ▸ hs ▸ ⟨rfl, hR⟩⟩
  · -- guard+guard+modify(count-1)
    apply L1_hoare_seq_ok (R := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧ heapPtrValid s.globals.rawHeap s.locals.out_val ∧ heapPtrValid s.globals.rawHeap s.locals.front)
    · apply L1_hoare_guard_guard_modify_fused
      · intro s ⟨hrb, _, _⟩
        exact hrb
      · intro s ⟨hrb, hov, hfront⟩
        dsimp only
        exact ⟨rfl, heapUpdate_preserves_heapPtrValid _ _ _ _ hrb, heapUpdate_preserves_heapPtrValid _ _ _ _ hov, heapUpdate_preserves_heapPtrValid _ _ _ _ hfront⟩
    · -- guard+modify(front.next:=null)
      apply L1_hoare_seq_ok (R := fun s => heapPtrValid s.globals.rawHeap s.locals.out_val)
      · apply L1_hoare_guard_modify_fused
        · intro s ⟨_, _, hfront⟩
          exact hfront
        · intro s ⟨_, hov, _⟩
          dsimp only
          exact ⟨rfl, heapUpdate_preserves_heapPtrValid _ _ _ _ hov⟩
      · -- modify(ret:=0) + throw
        intro s₀ hov
        have h := L1_modify_throw_result (fun s : ProgramState => setRetVal₂ s 0) s₀
        exact ⟨h.2, fun r s' h_mem => by
          rw [h.1] at h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem
          subst hr; subst hs
          exact hQ _ (setRetVal₂_retval s₀ 0) (setRetVal₂_globals s₀ 0 ▸ setRetVal₂_outval s₀ 0 ▸ hov)⟩

-- Part 2: steps 2-3 (guard+guard+modify, guard+guard+modify) + delegation
set_option maxRecDepth 4096 in
set_option maxHeartbeats 25600000 in
private theorem rb_pop_part2 (m : L1Monad ProgramState) (Q : Except Unit Unit → ProgramState → Prop) (h_tail : validHoare pop3v m Q) :
    validHoare (fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧ heapPtrValid s.globals.rawHeap s.locals.out_val ∧ heapPtrValid s.globals.rawHeap s.locals.front ∧ s.locals.front = (hVal s.globals.rawHeap s.locals.rb).head) (L1.seq (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.out_val)) (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.front)) (L1.modify (fun s => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.out_val ((hVal s.globals.rawHeap s.locals.front).value) } })))) (L1.seq (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.rb)) (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.front)) (L1.modify (fun s => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.rb ({ hVal s.globals.rawHeap s.locals.rb with head := (hVal s.globals.rawHeap s.locals.front).next }) } })))) m)) Q := by
  apply L1_hoare_seq_ok (R := pop3v)
  · apply L1_hoare_seq_ok (R := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧ heapPtrValid s.globals.rawHeap s.locals.out_val ∧ heapPtrValid s.globals.rawHeap s.locals.front ∧ s.locals.front = (hVal s.globals.rawHeap s.locals.rb).head)
    · apply L1_hoare_pre (P := fun s => heapPtrValid s.globals.rawHeap s.locals.out_val ∧ (heapPtrValid s.globals.rawHeap s.locals.rb ∧ heapPtrValid s.globals.rawHeap s.locals.out_val ∧ heapPtrValid s.globals.rawHeap s.locals.front ∧ s.locals.front = (hVal s.globals.rawHeap s.locals.rb).head))
      · intro s ⟨hrb, hov, hfront, hfeq⟩
        exact ⟨hov, hrb, hov, hfront, hfeq⟩
      · exact L1_hoare_guard' _ _
    · apply L1_hoare_guard_modify_fused
      · intro s ⟨_, _, hfront, _⟩
        exact hfront
      · intro s ⟨hrb, hov, hfront, _⟩
        dsimp only
        show _ = _ ∧ pop3v _
        unfold pop3v
        exact ⟨rfl, heapUpdate_preserves_heapPtrValid _ _ _ _ hrb, heapUpdate_preserves_heapPtrValid _ _ _ _ hov, heapUpdate_preserves_heapPtrValid _ _ _ _ hfront⟩
  · apply L1_hoare_seq_ok (R := pop3v)
    · apply L1_hoare_seq_ok (R := pop3v)
      · apply L1_hoare_pre (P := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧ pop3v s)
        · intro s h
          exact ⟨h.1, h⟩
        · exact L1_hoare_guard' _ _
      · apply L1_hoare_guard_modify_fused
        · intro s ⟨_, _, hfront⟩
          exact hfront
        · intro s ⟨hrb, hov, hfront⟩
          dsimp only
          show _ = _ ∧ pop3v _
          unfold pop3v
          exact ⟨rfl, heapUpdate_preserves_heapPtrValid _ _ _ _ hrb, heapUpdate_preserves_heapPtrValid _ _ _ _ hov, heapUpdate_preserves_heapPtrValid _ _ _ _ hfront⟩
    · exact h_tail

-- Part 3: outer catch + condition + guard_modify_fused for step 1
set_option maxRecDepth 8192 in
set_option maxHeartbeats 51200000 in
theorem rb_pop_validHoare : rb_pop_spec.satisfiedBy RingBufferExt.l1_rb_pop_body := by
  unfold FuncSpec.satisfiedBy rb_pop_spec
  apply L1_hoare_catch (R := fun s => s.locals.ret__val = 0 ∧ heapPtrValid s.globals.rawHeap s.locals.out_val)
  · apply L1_hoare_seq (R := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧ heapPtrValid s.globals.rawHeap s.locals.out_val ∧ (hVal s.globals.rawHeap s.locals.rb).head ≠ Ptr.null ∧ heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
    · -- cond(head==null → ret1+throw, skip)
      apply L1_hoare_condition
      · intro s ⟨⟨_, _, hne, _⟩, hcond⟩
        simp only [decide_eq_true_eq] at hcond
        exact absurd hcond hne
      · intro s ⟨⟨hrb, hov, hne, hhead⟩, _⟩
        refine ⟨fun hf => hf, fun r s' hmem => ?_⟩
        have ⟨hr, hs⟩ := Prod.mk.inj hmem
        subst hr; subst hs
        exact ⟨hrb, hov, hne, hhead⟩
    · -- guard(rb) + modify(front := rb.head) + rest
      -- The body here is L1.seq (L1.seq (L1.guard _) (L1.modify _)) rest
      -- Use guard_modify_fused for the first part
      sorry
  · intro s ⟨hret, hov⟩
    exact ⟨fun hf => hf, fun r s' hmem => let ⟨hr, hs⟩ := Prod.mk.inj hmem; hr ▸ hs ▸ fun _ => ⟨hret, hov⟩⟩
end RbPopProof

theorem rb_increment_all_validHoare : rb_increment_all_spec.satisfiedBy RingBufferExt.l1_rb_increment_all_body := by sorry
theorem rb_swap_front_back_validHoare : rb_swap_front_back_spec.satisfiedBy RingBufferExt.l1_rb_swap_front_back_body := by sorry
theorem rb_replace_all_validHoare : rb_replace_all_spec.satisfiedBy RingBufferExt.l1_rb_replace_all_body := by sorry
theorem rb_fill_validHoare : rb_fill_spec.satisfiedBy RingBufferExt.l1_rb_fill_body := by sorry
theorem rb_reverse_validHoare : rb_reverse_spec.satisfiedBy RingBufferExt.l1_rb_reverse_body := by sorry
theorem rb_remove_first_match_validHoare : rb_remove_first_match_spec.satisfiedBy RingBufferExt.l1_rb_remove_first_match_body := by sorry
theorem rb_equal_validHoare : rb_equal_spec.satisfiedBy RingBufferExt.l1_rb_equal_body := by sorry
set_option maxRecDepth 8192 in
set_option maxHeartbeats 51200000 in
theorem rb_check_integrity_validHoare : rb_check_integrity_spec.satisfiedBy RingBufferExt.l1_rb_check_integrity_body := by
  unfold FuncSpec.satisfiedBy rb_check_integrity_spec
  -- Goal: validHoare (fun s => heapPtrValid rb ∧ LinkedListValid head) body (fun r s => r=ok → (ret=0∨ret=1) ∧ ...)
  -- Body is: L1.catch (L1.seq (L1.dynCom ...) (conditionals)) L1.skip
  -- Strategy: catch with R = (ret=0 ∨ ret=1), then skip passes it through
  sorry
private theorem C_UInt32_iter_typeTag_ne : @CType.typeTag UInt32 _ ≠ @CType.typeTag C_rb_iter _ := by decide
private theorem out_val_iter_disjoint {h : HeapRawState} {p : Ptr UInt32} {q : Ptr C_rb_iter} (hp : heapPtrValid h p) (hq : heapPtrValid h q) : ptrDisjoint p q := heapPtrValid_different_type_disjoint hp hq C_UInt32_iter_typeTag_ne
set_option maxRecDepth 8192 in
set_option maxHeartbeats 51200000 in
theorem rb_iter_next_validHoare : rb_iter_next_spec.satisfiedBy RingBufferExt.l1_rb_iter_next_body := by
  unfold FuncSpec.satisfiedBy rb_iter_next_spec
  let CatchR := fun s : ProgramState => (s.locals.ret__val = 0 ∨ s.locals.ret__val = 1) ∧ heapPtrValid s.globals.rawHeap s.locals.iter
  let IntermR := fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.iter ∧ heapPtrValid s.globals.rawHeap s.locals.out_val ∧ (hVal s.globals.rawHeap s.locals.iter).current ≠ Ptr.null ∧ heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.iter).current
  let PostAdv := fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.iter ∧ heapPtrValid s.globals.rawHeap s.locals.out_val
  apply L1_hoare_catch (R := CatchR)
  · apply L1_hoare_seq (R := IntermR)
    · apply L1_hoare_condition
      · apply L1_hoare_modify_throw_catch (Q_ok := IntermR) (R := CatchR)
        intro s ⟨⟨hiter, _, _⟩, _⟩; dsimp only [CatchR]; exact ⟨Or.inr rfl, hiter⟩
      · intro s₀ ⟨⟨hiter, hout, hcur_impl⟩, hcond⟩
        simp only [decide_eq_false_iff_not] at hcond
        constructor
        · intro hf; exact hf
        · intro r s₁ hmem
          have ⟨hr, hs⟩ := Prod.mk.inj hmem; subst hr; subst hs
          exact ⟨hiter, hout, hcond, hcur_impl hcond⟩
    · apply L1_hoare_seq_ok (R := IntermR)
      · apply L1_hoare_seq_ok (R := IntermR)
        · apply L1_hoare_pre (P := fun s => heapPtrValid s.globals.rawHeap s.locals.out_val ∧ IntermR s)
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
                   by rw [hVal_heapUpdate_disjoint _ _ _ _ hbo hbi h_disj]; exact heapUpdate_preserves_heapPtrValid _ _ _ _ hcur⟩
      · apply L1_hoare_seq_ok (R := PostAdv)
        · apply L1_hoare_seq_ok (R := IntermR)
          · apply L1_hoare_pre (P := fun s => heapPtrValid s.globals.rawHeap s.locals.iter ∧ IntermR s)
            · intro s h; exact ⟨h.1, h⟩
            · exact L1_hoare_guard' _ _
          · apply L1_hoare_guard_modify_fused
            · intro s h; exact h.2.2.2
            · intro s ⟨hiter, hout, _, _⟩
              dsimp only
              constructor; · rfl
              show PostAdv _
              exact ⟨heapUpdate_preserves_heapPtrValid _ _ _ _ hiter, heapUpdate_preserves_heapPtrValid _ _ _ _ hout⟩
        · apply L1_hoare_seq (R := PostAdv)
          · apply L1_hoare_condition
            · apply L1_hoare_guard_guard_modify_fused
              · intro s ⟨h, _⟩; exact h.1
              · intro s ⟨⟨hiter, hout⟩, _⟩
                dsimp only
                show PostAdv _
                exact ⟨heapUpdate_preserves_heapPtrValid _ _ _ _ hiter, heapUpdate_preserves_heapPtrValid _ _ _ _ hout⟩
            · intro s₀ ⟨⟨hiter, hout⟩, _⟩
              constructor
              · intro hf; exact hf
              · intro r s₁ hmem
                have ⟨hr, hs⟩ := Prod.mk.inj hmem; subst hr; subst hs
                exact ⟨hiter, hout⟩
          · apply L1_hoare_modify_throw_catch (R := CatchR)
            intro s ⟨hiter, _⟩; dsimp only [CatchR]; exact ⟨Or.inl rfl, hiter⟩
  · intro s ⟨hret, hiter⟩
    constructor
    · intro hf; exact hf
    · intro r s' hmem
      have ⟨hr, hs⟩ := Prod.mk.inj hmem; subst hr; subst hs
      intro _; exact ⟨hret, hiter⟩
theorem rb_iter_skip_validHoare : rb_iter_skip_spec.satisfiedBy RingBufferExt.l1_rb_iter_skip_body := by sorry
theorem rb_push_if_not_full_validHoare : rb_push_if_not_full_spec.satisfiedBy RingBufferExt.l1_rb_push_if_not_full_body := by sorry
theorem rb_pop_if_not_empty_validHoare : rb_pop_if_not_empty_spec.satisfiedBy RingBufferExt.l1_rb_pop_if_not_empty_body := by sorry
theorem rb_drain_to_validHoare : rb_drain_to_spec.satisfiedBy RingBufferExt.l1_rb_drain_to_body := by sorry
theorem rb_clear_validHoare : rb_clear_spec.satisfiedBy RingBufferExt.l1_rb_clear_body := by sorry
