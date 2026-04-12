-- Proof for rb_iter_next_validHoare (split from RBExtProofsSorry)
import Examples.RBExtSpecs
set_option maxHeartbeats 25600000
set_option maxRecDepth 4096
open RingBufferExt
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
