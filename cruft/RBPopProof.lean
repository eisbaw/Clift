-- rb_pop validHoare proof.
-- Split into three parts; Part 3 uses opaque Locals setters to keep kernel depth low.

import Examples.RingBufferExtProof
import Clift.Lifting.FuncSpec
import Clift.Lifting.L1HoareRules

open RingBufferExt

private def rb_pop_spec_local : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.rb ∧
    heapPtrValid s.globals.rawHeap s.locals.out_val ∧
    (hVal s.globals.rawHeap s.locals.rb).head ≠ Ptr.null ∧
    heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head
  post := fun r s =>
    r = Except.ok () →
    s.locals.ret__val = 0 ∧
    heapPtrValid s.globals.rawHeap s.locals.out_val

private abbrev pop3v (s : ProgramState) : Prop :=
  heapPtrValid s.globals.rawHeap s.locals.rb ∧
  heapPtrValid s.globals.rawHeap s.locals.out_val ∧
  heapPtrValid s.globals.rawHeap s.locals.front

-- Opaque Locals setters to avoid 40-field struct expansion in kernel
@[irreducible] private def setRetVal (s : ProgramState) (v : UInt32) : ProgramState :=
  { s with locals := { s.locals with ret__val := v } }
@[irreducible] private def setFront (s : ProgramState) (v : Ptr C_rb_node) : ProgramState :=
  { s with locals := { s.locals with front := v } }

-- Projection lemmas
@[simp] private theorem setRetVal_globals (s v) : (setRetVal s v).globals = s.globals := by unfold setRetVal; rfl
@[simp] private theorem setRetVal_retval (s v) : (setRetVal s v).locals.ret__val = v := by unfold setRetVal; rfl
@[simp] private theorem setRetVal_outval (s v) : (setRetVal s v).locals.out_val = s.locals.out_val := by unfold setRetVal; rfl
@[simp] private theorem setRetVal_rb (s v) : (setRetVal s v).locals.rb = s.locals.rb := by unfold setRetVal; rfl
@[simp] private theorem setRetVal_front (s v) : (setRetVal s v).locals.front = s.locals.front := by unfold setRetVal; rfl
@[simp] private theorem setFront_globals (s v) : (setFront s v).globals = s.globals := by unfold setFront; rfl
@[simp] private theorem setFront_front (s v) : (setFront s v).locals.front = v := by unfold setFront; rfl
@[simp] private theorem setFront_rb (s v) : (setFront s v).locals.rb = s.locals.rb := by unfold setFront; rfl
@[simp] private theorem setFront_outval (s v) : (setFront s v).locals.out_val = s.locals.out_val := by unfold setFront; rfl

-- Body equivalence: raw struct update = opaque setter
private theorem setRetVal_eq (s : ProgramState) (v : UInt32) :
    { s with locals := { s.locals with ret__val := v } } = setRetVal s v := by unfold setRetVal; rfl
private theorem setFront_eq (s : ProgramState) (v : Ptr C_rb_node) :
    { s with locals := { s.locals with front := v } } = setFront s v := by unfold setFront; rfl

attribute [local irreducible] hVal heapUpdate

-- Part 1: Steps 4-7 (only Globals updates, no Locals depth issue)
set_option maxRecDepth 4096 in
set_option maxHeartbeats 25600000 in
private theorem rb_pop_part1 (m : L1Monad ProgramState) (Q : Except Unit Unit → ProgramState → Prop)
    (hm : m = L1.seq (L1.condition (fun s => decide ((hVal s.globals.rawHeap s.locals.rb).head = @Ptr.null C_rb_node)) (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.rb)) (L1.modify (fun s => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.rb ({ hVal s.globals.rawHeap s.locals.rb with tail := @Ptr.null C_rb_node }) } }))) L1.skip) (L1.seq (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.rb)) (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.rb)) (L1.modify (fun s => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.rb ({ hVal s.globals.rawHeap s.locals.rb with count := (hVal s.globals.rawHeap s.locals.rb).count - 1 }) } })))) (L1.seq (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.front)) (L1.modify (fun s => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.front ({ hVal s.globals.rawHeap s.locals.front with next := @Ptr.null C_rb_node }) } }))) (L1.seq (L1.modify (fun s => setRetVal s 0)) L1.throw))))
    (hQ : ∀ s, s.locals.ret__val = 0 → heapPtrValid s.globals.rawHeap s.locals.out_val → Q (Except.error ()) s) :
    validHoare pop3v m Q := by
  subst hm; unfold pop3v
  apply L1_hoare_seq_ok (R := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧ heapPtrValid s.globals.rawHeap s.locals.out_val ∧ heapPtrValid s.globals.rawHeap s.locals.front)
  · apply L1_hoare_condition'
    · apply L1_hoare_pre (P := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧ heapPtrValid s.globals.rawHeap s.locals.out_val ∧ heapPtrValid s.globals.rawHeap s.locals.front)
      · intro s ⟨hpre, _⟩; exact hpre
      · apply L1_hoare_guard_modify_fused
        · intro s ⟨hrb, _, _⟩; exact hrb
        · intro s ⟨hrb, hov, hfront⟩; dsimp only; exact ⟨rfl, heapUpdate_preserves_heapPtrValid _ _ _ _ hrb, heapUpdate_preserves_heapPtrValid _ _ _ _ hov, heapUpdate_preserves_heapPtrValid _ _ _ _ hfront⟩
    · apply L1_hoare_pre (P := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧ heapPtrValid s.globals.rawHeap s.locals.out_val ∧ heapPtrValid s.globals.rawHeap s.locals.front)
      · intro s ⟨hpre, _⟩; exact hpre
      · intro s hR; exact ⟨fun hf => hf, fun r s' hmem => let ⟨hr, hs⟩ := Prod.mk.inj hmem; hr ▸ hs ▸ ⟨rfl, hR⟩⟩
  · apply L1_hoare_seq_ok (R := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧ heapPtrValid s.globals.rawHeap s.locals.out_val ∧ heapPtrValid s.globals.rawHeap s.locals.front)
    · apply L1_hoare_guard_guard_modify_fused
      · intro s ⟨hrb, _, _⟩; exact hrb
      · intro s ⟨hrb, hov, hfront⟩; dsimp only; exact ⟨rfl, heapUpdate_preserves_heapPtrValid _ _ _ _ hrb, heapUpdate_preserves_heapPtrValid _ _ _ _ hov, heapUpdate_preserves_heapPtrValid _ _ _ _ hfront⟩
    · apply L1_hoare_seq_ok (R := fun s => heapPtrValid s.globals.rawHeap s.locals.out_val)
      · apply L1_hoare_guard_modify_fused
        · intro s ⟨_, _, hfront⟩; exact hfront
        · intro s ⟨_, hov, _⟩; dsimp only; exact ⟨rfl, heapUpdate_preserves_heapPtrValid _ _ _ _ hov⟩
      · intro s₀ hov
        have h := L1_modify_throw_result (fun s : ProgramState => setRetVal s 0) s₀
        exact ⟨h.2, fun r s' h_mem => by rw [h.1] at h_mem; have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs; simp only [setRetVal_retval, setRetVal_globals, setRetVal_outval]; exact hQ _ rfl hov⟩

-- Part 2: Steps 2-3 + delegation
set_option maxRecDepth 4096 in
set_option maxHeartbeats 25600000 in
private theorem rb_pop_part2
    (m : L1Monad ProgramState) (Q : Except Unit Unit → ProgramState → Prop)
    (h_tail : validHoare pop3v m Q) :
    validHoare (fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧ heapPtrValid s.globals.rawHeap s.locals.out_val ∧ heapPtrValid s.globals.rawHeap s.locals.front ∧ s.locals.front = (hVal s.globals.rawHeap s.locals.rb).head)
    (L1.seq (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.out_val)) (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.front)) (L1.modify (fun s => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.out_val ((hVal s.globals.rawHeap s.locals.front).value) } })))) (L1.seq (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.rb)) (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.front)) (L1.modify (fun s => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.rb ({ hVal s.globals.rawHeap s.locals.rb with head := (hVal s.globals.rawHeap s.locals.front).next }) } })))) m))
    Q := by
  apply L1_hoare_seq_ok (R := pop3v)
  · apply L1_hoare_seq_ok (R := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧ heapPtrValid s.globals.rawHeap s.locals.out_val ∧ heapPtrValid s.globals.rawHeap s.locals.front ∧ s.locals.front = (hVal s.globals.rawHeap s.locals.rb).head)
    · apply L1_hoare_pre (P := fun s => heapPtrValid s.globals.rawHeap s.locals.out_val ∧ (heapPtrValid s.globals.rawHeap s.locals.rb ∧ heapPtrValid s.globals.rawHeap s.locals.out_val ∧ heapPtrValid s.globals.rawHeap s.locals.front ∧ s.locals.front = (hVal s.globals.rawHeap s.locals.rb).head))
      · intro s ⟨hrb, hov, hfront, hfeq⟩; exact ⟨hov, hrb, hov, hfront, hfeq⟩
      · exact L1_hoare_guard' _ _
    · apply L1_hoare_guard_modify_fused
      · intro s ⟨_, _, hfront, _⟩; exact hfront
      · intro s ⟨hrb, hov, hfront, _⟩; dsimp only; show _ = _ ∧ pop3v _; unfold pop3v; exact ⟨rfl, heapUpdate_preserves_heapPtrValid _ _ _ _ hrb, heapUpdate_preserves_heapPtrValid _ _ _ _ hov, heapUpdate_preserves_heapPtrValid _ _ _ _ hfront⟩
  · apply L1_hoare_seq_ok (R := pop3v)
    · apply L1_hoare_seq_ok (R := pop3v)
      · apply L1_hoare_pre (P := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧ pop3v s)
        · intro s h; exact ⟨h.1, h⟩
        · exact L1_hoare_guard' _ _
      · apply L1_hoare_guard_modify_fused
        · intro s ⟨_, _, hfront⟩; exact hfront
        · intro s ⟨hrb, hov, hfront⟩; dsimp only; show _ = _ ∧ pop3v _; unfold pop3v; exact ⟨rfl, heapUpdate_preserves_heapPtrValid _ _ _ _ hrb, heapUpdate_preserves_heapPtrValid _ _ _ _ hov, heapUpdate_preserves_heapPtrValid _ _ _ _ hfront⟩
    · exact h_tail

-- Part 3: catch + cond + step 1 (uses opaque setRetVal/setFront for Locals updates)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 51200000 in
theorem rb_pop_validHoare_proven :
    rb_pop_spec_local.satisfiedBy RingBufferExt.l1_rb_pop_body := by
  unfold FuncSpec.satisfiedBy rb_pop_spec_local
  -- Rewrite the Locals-updating modify calls to use opaque setters
  have h_body_eq : RingBufferExt.l1_rb_pop_body = (RingBufferExt.l1_rb_pop_body) := rfl
  apply L1_hoare_catch (R := fun s => s.locals.ret__val = 0 ∧ heapPtrValid s.globals.rawHeap s.locals.out_val)
  · apply L1_hoare_seq (R := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧ heapPtrValid s.globals.rawHeap s.locals.out_val ∧ (hVal s.globals.rawHeap s.locals.rb).head ≠ Ptr.null ∧ heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
    · -- Cond: head=null → {ret=1;throw}, else skip
      -- Use conv to rewrite the inner modify to use setRetVal
      apply L1_hoare_condition
      · intro s ⟨⟨_, _, hne, _⟩, hcond⟩; simp only [decide_eq_true_eq] at hcond; exact absurd hcond hne
      · intro s ⟨⟨hrb, hov, hne, hhead⟩, _⟩; exact ⟨fun hf => hf, fun r s' hmem => let ⟨hr, hs⟩ := Prod.mk.inj hmem; hr ▸ hs ▸ ⟨hrb, hov, hne, hhead⟩⟩
    · -- Step 1: guard(rbV); modify(front := rb.head)
      -- Rewrite modify to use setFront
      show validHoare _ (L1.seq (L1.guard _) (L1.seq (L1.modify _) _)) _
      apply L1_hoare_seq_ok (R := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧ heapPtrValid s.globals.rawHeap s.locals.out_val ∧ heapPtrValid s.globals.rawHeap s.locals.front ∧ s.locals.front = (hVal s.globals.rawHeap s.locals.rb).head)
      · apply L1_hoare_guard_modify_fused
        · intro s ⟨hrb, _, _, _⟩; exact hrb
        · intro s ⟨hrb, hov, _, hhead⟩; dsimp only; exact ⟨rfl, hrb, hov, hhead, rfl⟩
      · exact rb_pop_part2 _ _ (rb_pop_part1 _ _ rfl (fun s hret hov => ⟨hret, hov⟩))
  · intro s ⟨hret, hov⟩; exact ⟨fun hf => hf, fun r s' hmem => let ⟨hr, hs⟩ := Prod.mk.inj hmem; hr ▸ hs ▸ fun _ => ⟨hret, hov⟩⟩
