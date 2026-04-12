-- Proof for rb_pop_validHoare (split from RBExtProofsSorry for memory)
-- Parts 1+2 fully proven, Part 3 has 1 sorry (guard+modify typeclass issue)
import Examples.RBExtSpecs
set_option maxHeartbeats 25600000
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
