-- Sorry (not yet proven) validHoare theorems for ring buffer functions.
-- Split from RBExtFuncSpecs.lean (task 0233).
--
-- 14 sorry remaining (rb_iter_next proved):
--   Multi-heap: rb_pop, rb_swap_front_back
--   Loop+mutation: rb_increment_all, rb_replace_all, rb_fill, rb_reverse,
--                  rb_remove_first_match, rb_clear
--   Dual-pointer loop: rb_equal
--   Inter-procedural: rb_check_integrity, rb_iter_skip,
--                     rb_push_if_not_full, rb_pop_if_not_empty, rb_drain_to

import Examples.RBExtSpecs

set_option maxHeartbeats 12800000
set_option maxRecDepth 4096

open RingBufferExt

-- Helper abbreviation: three pointer validity facts for rb_pop
private abbrev pop3v (s : ProgramState) : Prop :=
  heapPtrValid s.globals.rawHeap s.locals.rb ∧
  heapPtrValid s.globals.rawHeap s.locals.out_val ∧
  heapPtrValid s.globals.rawHeap s.locals.front

attribute [local irreducible] hVal heapUpdate

-- Part 1: Steps 4-7 of rb_pop body
set_option maxRecDepth 4096 in
set_option maxHeartbeats 25600000 in
private theorem rb_pop_part1 (m : L1Monad ProgramState) (Q : Except Unit Unit → ProgramState → Prop)
    (hm : m = L1.seq (L1.condition (fun s => decide ((hVal s.globals.rawHeap s.locals.rb).head = @Ptr.null C_rb_node)) (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.rb)) (L1.modify (fun s => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.rb ({ hVal s.globals.rawHeap s.locals.rb with tail := @Ptr.null C_rb_node }) } }))) L1.skip) (L1.seq (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.rb)) (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.rb)) (L1.modify (fun s => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.rb ({ hVal s.globals.rawHeap s.locals.rb with count := (hVal s.globals.rawHeap s.locals.rb).count - 1 }) } })))) (L1.seq (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.front)) (L1.modify (fun s => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.front ({ hVal s.globals.rawHeap s.locals.front with next := @Ptr.null C_rb_node }) } }))) (L1.seq (L1.modify (fun s => { s with locals := { s.locals with ret__val := 0 } })) L1.throw))))
    (hQ : ∀ s, s.locals.ret__val = 0 → heapPtrValid s.globals.rawHeap s.locals.out_val →
      Q (Except.error ()) s) :
    validHoare pop3v m Q := by
  subst hm; unfold pop3v
  apply L1_hoare_seq_ok (R := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.rb ∧
    heapPtrValid s.globals.rawHeap s.locals.out_val ∧
    heapPtrValid s.globals.rawHeap s.locals.front)
  · apply L1_hoare_condition'
    · apply L1_hoare_pre (P := fun s =>
        heapPtrValid s.globals.rawHeap s.locals.rb ∧
        heapPtrValid s.globals.rawHeap s.locals.out_val ∧
        heapPtrValid s.globals.rawHeap s.locals.front)
      · intro s ⟨hpre, _⟩; exact hpre
      · apply L1_hoare_guard_modify_fused
        · intro s ⟨hrb, _, _⟩; exact hrb
        · intro s ⟨hrb, hov, hfront⟩; dsimp only
          exact ⟨rfl, heapUpdate_preserves_heapPtrValid _ _ _ _ hrb,
                 heapUpdate_preserves_heapPtrValid _ _ _ _ hov,
                 heapUpdate_preserves_heapPtrValid _ _ _ _ hfront⟩
    · apply L1_hoare_pre (P := fun s =>
        heapPtrValid s.globals.rawHeap s.locals.rb ∧
        heapPtrValid s.globals.rawHeap s.locals.out_val ∧
        heapPtrValid s.globals.rawHeap s.locals.front)
      · intro s ⟨hpre, _⟩; exact hpre
      · intro s hR; exact ⟨fun hf => hf, fun r s' hmem =>
          let ⟨hr, hs⟩ := Prod.mk.inj hmem; hr ▸ hs ▸ ⟨rfl, hR⟩⟩
  · apply L1_hoare_seq_ok (R := fun s =>
      heapPtrValid s.globals.rawHeap s.locals.rb ∧
      heapPtrValid s.globals.rawHeap s.locals.out_val ∧
      heapPtrValid s.globals.rawHeap s.locals.front)
    · apply L1_hoare_guard_guard_modify_fused
      · intro s ⟨hrb, _, _⟩; exact hrb
      · intro s ⟨hrb, hov, hfront⟩; dsimp only
        exact ⟨rfl, heapUpdate_preserves_heapPtrValid _ _ _ _ hrb,
               heapUpdate_preserves_heapPtrValid _ _ _ _ hov,
               heapUpdate_preserves_heapPtrValid _ _ _ _ hfront⟩
    · apply L1_hoare_seq_ok (R := fun s =>
        heapPtrValid s.globals.rawHeap s.locals.out_val)
      · apply L1_hoare_guard_modify_fused
        · intro s ⟨_, _, hfront⟩; exact hfront
        · intro s ⟨_, hov, _⟩; dsimp only
          exact ⟨rfl, heapUpdate_preserves_heapPtrValid _ _ _ _ hov⟩
      · intro s₀ hov
        have h := L1_modify_throw_result
          (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } }) s₀
        exact ⟨h.2, fun r s' h_mem => by
          rw [h.1] at h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
          exact hQ _ rfl hov⟩

-- Part 2: Steps 2-3 of rb_pop body + delegation to Part 1
set_option maxRecDepth 4096 in
set_option maxHeartbeats 25600000 in
private theorem rb_pop_part2
    (m : L1Monad ProgramState) (Q : Except Unit Unit → ProgramState → Prop)
    (h_tail : validHoare pop3v m Q) :
    validHoare (fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧ heapPtrValid s.globals.rawHeap s.locals.out_val ∧ heapPtrValid s.globals.rawHeap s.locals.front ∧ s.locals.front = (hVal s.globals.rawHeap s.locals.rb).head)
    (L1.seq (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.out_val)) (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.front)) (L1.modify (fun s => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.out_val ((hVal s.globals.rawHeap s.locals.front).value) } })))) (L1.seq (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.rb)) (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.front)) (L1.modify (fun s => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.rb ({ hVal s.globals.rawHeap s.locals.rb with head := (hVal s.globals.rawHeap s.locals.front).next }) } })))) m))
    Q := by
  apply L1_hoare_seq_ok (R := pop3v)
  · apply L1_hoare_seq_ok (R := fun s =>
      heapPtrValid s.globals.rawHeap s.locals.rb ∧
      heapPtrValid s.globals.rawHeap s.locals.out_val ∧
      heapPtrValid s.globals.rawHeap s.locals.front ∧
      s.locals.front = (hVal s.globals.rawHeap s.locals.rb).head)
    · apply L1_hoare_pre (P := fun s =>
        heapPtrValid s.globals.rawHeap s.locals.out_val ∧
        (heapPtrValid s.globals.rawHeap s.locals.rb ∧
         heapPtrValid s.globals.rawHeap s.locals.out_val ∧
         heapPtrValid s.globals.rawHeap s.locals.front ∧
         s.locals.front = (hVal s.globals.rawHeap s.locals.rb).head))
      · intro s ⟨hrb, hov, hfront, hfeq⟩; exact ⟨hov, hrb, hov, hfront, hfeq⟩
      · exact L1_hoare_guard' _ _
    · apply L1_hoare_guard_modify_fused
      · intro s ⟨_, _, hfront, _⟩; exact hfront
      · intro s ⟨hrb, hov, hfront, _⟩; dsimp only
        show _ = _ ∧ pop3v _; unfold pop3v
        exact ⟨rfl, heapUpdate_preserves_heapPtrValid _ _ _ _ hrb,
               heapUpdate_preserves_heapPtrValid _ _ _ _ hov,
               heapUpdate_preserves_heapPtrValid _ _ _ _ hfront⟩
  · apply L1_hoare_seq_ok (R := pop3v)
    · apply L1_hoare_seq_ok (R := pop3v)
      · apply L1_hoare_pre (P := fun s =>
          heapPtrValid s.globals.rawHeap s.locals.rb ∧ pop3v s)
        · intro s h; exact ⟨h.1, h⟩
        · exact L1_hoare_guard' _ _
      · apply L1_hoare_guard_modify_fused
        · intro s ⟨_, _, hfront⟩; exact hfront
        · intro s ⟨hrb, hov, hfront⟩; dsimp only
          show _ = _ ∧ pop3v _; unfold pop3v
          exact ⟨rfl, heapUpdate_preserves_heapPtrValid _ _ _ _ hrb,
                 heapUpdate_preserves_heapPtrValid _ _ _ _ hov,
                 heapUpdate_preserves_heapPtrValid _ _ _ _ hfront⟩
    · exact h_tail

-- Part 3: Outer catch + cond(head==null) + step 1
set_option maxRecDepth 8192 in
set_option maxHeartbeats 51200000 in
theorem rb_pop_validHoare :
    rb_pop_spec.satisfiedBy RingBufferExt.l1_rb_pop_body := by
  unfold FuncSpec.satisfiedBy rb_pop_spec
  apply L1_hoare_catch (R := fun s =>
    s.locals.ret__val = 0 ∧ heapPtrValid s.globals.rawHeap s.locals.out_val)
  · apply L1_hoare_seq (R := fun s =>
      heapPtrValid s.globals.rawHeap s.locals.rb ∧
      heapPtrValid s.globals.rawHeap s.locals.out_val ∧
      (hVal s.globals.rawHeap s.locals.rb).head ≠ Ptr.null ∧
      heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
    · apply L1_hoare_condition
      · intro s ⟨⟨_, _, hne, _⟩, hcond⟩
        simp only [decide_eq_true_eq] at hcond
        exact absurd hcond hne
      · intro s ⟨⟨hrb, hov, hne, hhead⟩, _⟩
        constructor
        · intro hf; exact hf
        · intro r s' hmem
          have ⟨hr, hs⟩ := Prod.mk.inj hmem; subst hr; subst hs
          exact ⟨hrb, hov, hne, hhead⟩
    · apply L1_hoare_seq_ok (R := fun s =>
        heapPtrValid s.globals.rawHeap s.locals.rb ∧
        heapPtrValid s.globals.rawHeap s.locals.out_val ∧
        heapPtrValid s.globals.rawHeap s.locals.front ∧
        s.locals.front = (hVal s.globals.rawHeap s.locals.rb).head)
      · apply L1_hoare_guard_modify_fused
        · intro s ⟨hrb, _, _, _⟩; exact hrb
        · intro s ⟨hrb, hov, _, hhead⟩; dsimp only
          exact ⟨rfl, hrb, hov, hhead, rfl⟩
      · exact rb_pop_part2 _ _
          (rb_pop_part1 _ _ rfl (fun s hret hov => ⟨hret, hov⟩))
  · intro s ⟨hret, hov⟩
    exact ⟨fun hf => hf, fun r s' hmem =>
      let ⟨hr, hs⟩ := Prod.mk.inj hmem; hr ▸ hs ▸ fun _ => ⟨hret, hov⟩⟩

theorem rb_increment_all_validHoare :
    rb_increment_all_spec.satisfiedBy RingBufferExt.l1_rb_increment_all_body := by
  sorry

theorem rb_swap_front_back_validHoare :
    rb_swap_front_back_spec.satisfiedBy RingBufferExt.l1_rb_swap_front_back_body := by
  sorry

theorem rb_replace_all_validHoare :
    rb_replace_all_spec.satisfiedBy RingBufferExt.l1_rb_replace_all_body := by
  sorry

theorem rb_fill_validHoare :
    rb_fill_spec.satisfiedBy RingBufferExt.l1_rb_fill_body := by
  sorry

theorem rb_reverse_validHoare :
    rb_reverse_spec.satisfiedBy RingBufferExt.l1_rb_reverse_body := by
  sorry

theorem rb_remove_first_match_validHoare :
    rb_remove_first_match_spec.satisfiedBy RingBufferExt.l1_rb_remove_first_match_body := by
  sorry

theorem rb_equal_validHoare :
    rb_equal_spec.satisfiedBy RingBufferExt.l1_rb_equal_body := by
  sorry

-- rb_check_integrity: calls rb_count_nodes via dynCom + L1.call l1ProcEnv.
-- The postcondition is tautological: (ret=0 v ret=1) AND (count = count).
-- However, the L1 body inlines l1_rb_count_nodes_body (via L1.call l1ProcEnv),
-- which contains a while loop with guard(heapPtrValid cur). This guard can fail
-- if the linked list is not well-formed. The spec precondition (heapPtrValid rb)
-- is insufficient to guarantee non-failure. validHoare requires not-failed, so
-- this theorem needs LinkedListValid in the precondition.
theorem rb_check_integrity_validHoare :
    rb_check_integrity_spec.satisfiedBy RingBufferExt.l1_rb_check_integrity_body := by
  sorry

-- rb_iter_next: conditional + guard+modify chain (no loops, no calls)
-- Structure: catch(seq(cond(null->ret1+throw,skip), guard_chain+ret0+throw), skip)
-- Both paths set ret to 0 or 1 and throw, caught by skip.
-- Type disjointness: UInt32(tag 1) vs C_rb_iter(tag 203) vs C_rb_node(tag 200).

private theorem C_UInt32_iter_typeTag_ne :
    @CType.typeTag UInt32 _ ≠ @CType.typeTag C_rb_iter _ := by decide

private theorem out_val_iter_disjoint {h : HeapRawState} {p : Ptr UInt32} {q : Ptr C_rb_iter}
    (hp : heapPtrValid h p) (hq : heapPtrValid h q) :
    ptrDisjoint p q :=
  heapPtrValid_different_type_disjoint hp hq C_UInt32_iter_typeTag_ne

set_option maxRecDepth 8192 in
set_option maxHeartbeats 51200000 in
theorem rb_iter_next_validHoare :
    rb_iter_next_spec.satisfiedBy RingBufferExt.l1_rb_iter_next_body := by
  unfold FuncSpec.satisfiedBy rb_iter_next_spec
  -- Abbreviations for intermediate state predicates
  let CatchR := fun s : ProgramState =>
    (s.locals.ret__val = 0 ∨ s.locals.ret__val = 1) ∧
    heapPtrValid s.globals.rawHeap s.locals.iter
  let IntermR := fun s : ProgramState =>
    heapPtrValid s.globals.rawHeap s.locals.iter ∧
    heapPtrValid s.globals.rawHeap s.locals.out_val ∧
    (hVal s.globals.rawHeap s.locals.iter).current ≠ Ptr.null ∧
    heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.iter).current
  let PostAdv := fun s : ProgramState =>
    heapPtrValid s.globals.rawHeap s.locals.iter ∧
    heapPtrValid s.globals.rawHeap s.locals.out_val
  -- Structure: L1.catch body L1.skip. Both branches throw, caught by skip.
  apply L1_hoare_catch (R := CatchR)
  · -- Body: seq(cond(null check), rest_chain)
    apply L1_hoare_seq (R := IntermR)
    · -- cond(current==null, modify(ret:=1)+throw, skip)
      apply L1_hoare_condition
      · -- True: current==null -> seq(modify ret:=1, throw) -> error with CatchR
        apply L1_hoare_modify_throw_catch
          (Q_ok := IntermR)
          (R := CatchR)
        intro s ⟨⟨hiter, _, _⟩, _⟩
        dsimp only [CatchR]
        exact ⟨Or.inr rfl, hiter⟩
      · -- False: current != null -> skip (preserves pre)
        intro s₀ ⟨⟨hiter, hout, hcur_impl⟩, hcond⟩
        simp only [decide_eq_false_iff_not] at hcond
        constructor
        · intro hf; exact hf
        · intro r s₁ hmem
          have ⟨hr, hs⟩ := Prod.mk.inj hmem; subst hr; subst hs
          exact ⟨hiter, hout, hcond, hcur_impl hcond⟩
    · -- rest: guard+guard+modify(write), guard+guard+modify(advance), cond(dec), modify(ret:=0)+throw
      -- Step 1: guard(out_val) >> guard(current) >> modify(*out_val := current->value)
      apply L1_hoare_seq_ok (R := IntermR)
      · -- Two different guards: decompose as guard then guard+modify
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
        apply L1_hoare_seq_ok (R := PostAdv)
        · -- Two different guards: decompose
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
        · -- Step 3: seq(cond(remaining>0, guard+guard+modify(dec), skip), seq(modify(ret:=0), throw))
          apply L1_hoare_seq (R := PostAdv)
          · apply L1_hoare_condition
            · -- True: remaining>0 -> guard(iter)+guard(iter)+modify(remaining-=1)
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
  · -- Handler: skip converts R to Q
    intro s ⟨hret, hiter⟩
    constructor
    · intro hf; exact hf
    · intro r s' hmem
      have ⟨hr, hs⟩ := Prod.mk.inj hmem; subst hr; subst hs
      intro _; exact ⟨hret, hiter⟩

theorem rb_iter_skip_validHoare :
    rb_iter_skip_spec.satisfiedBy RingBufferExt.l1_rb_iter_skip_body := by
  sorry

theorem rb_push_if_not_full_validHoare :
    rb_push_if_not_full_spec.satisfiedBy RingBufferExt.l1_rb_push_if_not_full_body := by
  sorry

theorem rb_pop_if_not_empty_validHoare :
    rb_pop_if_not_empty_spec.satisfiedBy RingBufferExt.l1_rb_pop_if_not_empty_body := by
  sorry

theorem rb_drain_to_validHoare :
    rb_drain_to_spec.satisfiedBy RingBufferExt.l1_rb_drain_to_body := by
  sorry

theorem rb_clear_validHoare :
    rb_clear_spec.satisfiedBy RingBufferExt.l1_rb_clear_body := by
  sorry
