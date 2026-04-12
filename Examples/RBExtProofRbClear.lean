-- Proof for rb_clear_validHoare (split from RBExtProofsSorry for memory)
import Examples.RBExtSpecs
set_option maxHeartbeats 25600000
set_option maxRecDepth 4096
open RingBufferExt

/-! # Helper lemmas -/

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem WellFormedList_heapUpdate_aux
    {heap : HeapRawState} {p : Ptr C_rb_node} {v : C_rb_node} {nxt : Ptr C_rb_node}
    (hwf : WellFormedList heap nxt) (hv : heapPtrValid heap p)
    (h_sep : AllDisjointFrom heap p nxt)
    : WellFormedList (heapUpdate heap p v) nxt := by
  induction hwf with
  | null => exact WellFormedList.null
  | @cons q hq hv_q _ hsep_q ih =>
    have h_eq_q := hVal_heapUpdate_disjoint heap p q v (heapPtrValid_bound hv)
      (heapPtrValid_bound hv_q) (h_sep.headDisjoint hq)
    exact WellFormedList.cons q hq (heapUpdate_preserves_heapPtrValid heap p v q hv_q)
      (h_eq_q ▸ ih (h_sep.adjtail hq))
      (h_eq_q ▸ AllDisjointFrom_heapUpdate_frame hsep_q (h_sep.adjtail hq) hv)

attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem AllDisjointFrom_heapUpdate_frame
    {heap : HeapRawState} {q r : Ptr C_rb_node} {v : C_rb_node} {p : Ptr C_rb_node}
    (hadj_q : AllDisjointFrom heap q p) (hadj_r : AllDisjointFrom heap r p)
    (hr : heapPtrValid heap r)
    : AllDisjointFrom (heapUpdate heap r v) q p := by
  induction hadj_q with
  | null => exact AllDisjointFrom.null
  | cons p' hp' hv' hdisj_qp' _ ih =>
    exact AllDisjointFrom.cons p' hp'
      (heapUpdate_preserves_heapPtrValid heap r v p' hv') hdisj_qp'
      (hVal_heapUpdate_disjoint heap r p' v (heapPtrValid_bound hr)
        (heapPtrValid_bound hv') (hadj_r.headDisjoint hp') ▸ ih (hadj_r.adjtail hp'))

attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem WellFormedList_heapUpdate_tail
    {heap : HeapRawState} {p : Ptr C_rb_node} {v : C_rb_node}
    (h : WellFormedList heap p) (hp : p ≠ Ptr.null) (hv : heapPtrValid heap p)
    : WellFormedList (heapUpdate heap p v) (hVal heap p).next :=
  WellFormedList_heapUpdate_aux (h.wf_tail hp) hv (h.headSep hp)

/-! # Loop invariant -/

private def rb_clear_inv (s : ProgramState) : Prop :=
  heapPtrValid s.globals.rawHeap s.locals.rb ∧
  WellFormedList s.globals.rawHeap s.locals.cur

/-! # Main theorem -/

set_option maxRecDepth 8192 in
set_option maxHeartbeats 102400000 in
attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem rb_clear_validHoare :
    rb_clear_spec_ext.satisfiedBy RingBufferExt.l1_rb_clear_body := by
  unfold FuncSpec.satisfiedBy rb_clear_spec_ext
  unfold RingBufferExt.l1_rb_clear_body
  -- Structure: catch body skip
  -- body = seq(modify rem:=0)(seq(guard rb; modify cur:=head)(seq(while ...)(postchain)))
  -- postchain = seq(guard rb; modify head:=null)(seq(guard rb; modify tail:=null)
  --             (seq(guard rb; modify count:=0)(seq(modify ret:=rem) throw)))
  -- Handler: skip
  --
  -- Use L1_hoare_catch with R = postcondition for the catch error branch.
  -- The body ends with throw, producing error. catch converts to ok.
  let PostR := fun s : ProgramState =>
    (hVal s.globals.rawHeap s.locals.rb).head = Ptr.null ∧
    (hVal s.globals.rawHeap s.locals.rb).tail = Ptr.null ∧
    (hVal s.globals.rawHeap s.locals.rb).count = 0
  apply L1_hoare_catch (R := PostR)
  · -- Body proof: use seq_ok for the ok-producing parts, then seq for throw-producing end
    -- First: modify rem:=0 (ok-only)
    apply L1_hoare_seq_ok (R := fun s =>
        heapPtrValid s.globals.rawHeap s.locals.rb ∧
        WellFormedList s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
    · -- modify removed:=0: pre must ensure R holds at (f s)
      -- f s = { s with locals := { s.locals with removed := 0 } }
      -- R(f s) = heapPtrValid (f s).heap (f s).rb ∧ WellFormedList (f s).heap (hVal ...).head
      -- Since (f s).globals = s.globals and (f s).locals.rb = s.locals.rb, R(f s) = R(s)
      -- So the precondition is just the original spec.pre
      intro s₀ ⟨hrb, hwf⟩
      constructor
      · intro hf; exact hf
      · intro r s₁ hmem
        have ⟨hr, hs⟩ := Prod.mk.inj hmem; subst hr; subst hs
        exact ⟨rfl, hrb, hwf⟩
    · -- Rest: guard+modify cur:=head, while, postchain
      apply L1_hoare_seq_ok (R := rb_clear_inv)
      · -- guard rb; modify cur:=head
        intro s₀ ⟨hrb, hwf⟩
        have h_gm := L1_guard_modify_result
          (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
          (fun s : ProgramState => { s with locals := { s.locals with
            cur := (hVal s.globals.rawHeap s.locals.rb).head } }) s₀ hrb
        constructor
        · exact h_gm.2
        · intro r s₁ hmem; rw [h_gm.1] at hmem
          have ⟨hr, hs⟩ := Prod.mk.inj hmem; subst hr; subst hs
          exact ⟨rfl, hrb, hwf⟩
      · -- while + postchain
        -- The while produces ok. Then the postchain produces error (throw).
        -- Use L1_hoare_seq: while (ok) → postchain (error → R)
        apply L1_hoare_seq (R := fun s => heapPtrValid s.globals.rawHeap s.locals.rb)
        · -- While loop
          apply L1_hoare_while (I := rb_clear_inv)
          · intro s h; exact h
          · -- h_body_nf
            intro s ⟨hrb, hwf⟩ hc
            have h_ne : s.locals.cur ≠ Ptr.null := by simp only [decide_eq_true_eq] at hc; exact hc
            have hv := hwf.headValid h_ne
            intro hf; change (_ ∨ _) at hf
            rcases hf with hf1 | ⟨s₁, hs₁, hf2⟩
            · change (_ ∨ _) at hf1
              rcases hf1 with hfg | ⟨_, _, hfm⟩
              · exact L1_guard_not_failed hv hfg
              · exact hfm
            · change (_ ∨ _) at hs₁
              rcases hs₁ with ⟨sg, hsg, hm⟩ | ⟨he, _⟩
              · rw [L1_guard_results hv] at hsg; have ⟨_, rfl⟩ := Prod.mk.inj hsg
                have ⟨_, rfl⟩ := Prod.mk.inj hm
                change (_ ∨ _) at hf2
                rcases hf2 with ⟨s₂, hs₂, hf3⟩ | ⟨he2, _⟩
                · change (_ ∨ _) at hs₂
                  rcases hs₂ with ⟨sg2, hsg2, hm2⟩ | ⟨he3, _⟩
                  · rw [L1_guard_results hv] at hsg2; have ⟨_, rfl⟩ := Prod.mk.inj hsg2
                    have ⟨_, rfl⟩ := Prod.mk.inj hm2
                    change (_ ∨ _) at hf3
                    rcases hf3 with ⟨s₃, hs₃, hf4⟩ | ⟨he4, _⟩
                    · have ⟨_, rfl⟩ := Prod.mk.inj hs₃; exact hf4
                    · exact absurd (Prod.mk.inj he4).1 (by intro h; cases h)
                  · exact absurd (Prod.mk.inj he3).1 (by intro h; cases h)
                · change (_ ∨ _) at he2
                  rcases he2 with hfg2 | ⟨_, _, hfm2⟩
                  · exact L1_guard_not_failed hv hfg2
                  · exact hfm2
              · exact absurd (Prod.mk.inj he).1 (by intro h; cases h)
          · -- h_body_inv
            intro s s' ⟨hrb, hwf⟩ hc hmem
            have h_ne : s.locals.cur ≠ Ptr.null := by simp only [decide_eq_true_eq] at hc; exact hc
            have hv := hwf.headValid h_ne
            change (_ ∨ _) at hmem
            rcases hmem with ⟨s₁, hs₁, r1⟩ | ⟨he, _⟩
            · change (_ ∨ _) at hs₁
              rcases hs₁ with ⟨sg, hsg, hm⟩ | ⟨he, _⟩
              · rw [L1_guard_results hv] at hsg; have ⟨_, rfl⟩ := Prod.mk.inj hsg
                have ⟨_, rfl⟩ := Prod.mk.inj hm
                change (_ ∨ _) at r1
                rcases r1 with ⟨s₂, hs₂, r2⟩ | ⟨he, _⟩
                · change (_ ∨ _) at hs₂
                  rcases hs₂ with ⟨sg2, hsg2, hm2⟩ | ⟨he, _⟩
                  · rw [L1_guard_results hv] at hsg2; have ⟨_, rfl⟩ := Prod.mk.inj hsg2
                    have ⟨_, rfl⟩ := Prod.mk.inj hm2
                    change (_ ∨ _) at r2
                    rcases r2 with ⟨s₃, hs₃, r3⟩ | ⟨he, _⟩
                    · have ⟨_, rfl⟩ := Prod.mk.inj hs₃
                      have ⟨_, rfl⟩ := Prod.mk.inj r3
                      exact ⟨heapUpdate_preserves_heapPtrValid _ _ _ _ hrb,
                             WellFormedList_heapUpdate_tail hwf h_ne hv⟩
                    · exact absurd (Prod.mk.inj he).1 (by intro h; cases h)
                  · exact absurd (Prod.mk.inj he).1 (by intro h; cases h)
                · exact absurd (Prod.mk.inj he).1 (by intro h; cases h)
              · exact absurd (Prod.mk.inj he).1 (by intro h; cases h)
            · exact absurd (Prod.mk.inj he).1 (by intro h; cases h)
          · -- h_exit
            intro s ⟨hrb, _⟩ _; exact hrb
          · -- h_abrupt: body produces no error
            intro s s' ⟨hrb, hwf⟩ hc herr
            have h_ne : s.locals.cur ≠ Ptr.null := by simp only [decide_eq_true_eq] at hc; exact hc
            have hv := hwf.headValid h_ne
            change (_ ∨ _) at herr
            rcases herr with ⟨s₁, hs₁, r1⟩ | ⟨he, _⟩
            · change (_ ∨ _) at hs₁
              rcases hs₁ with ⟨sg, hsg, hm⟩ | ⟨he, _⟩
              · rw [L1_guard_results hv] at hsg; have ⟨_, rfl⟩ := Prod.mk.inj hsg
                have ⟨_, rfl⟩ := Prod.mk.inj hm
                change (_ ∨ _) at r1
                rcases r1 with ⟨s₂, hs₂, r2⟩ | ⟨he, _⟩
                · change (_ ∨ _) at hs₂
                  rcases hs₂ with ⟨sg2, hsg2, hm2⟩ | ⟨he, _⟩
                  · rw [L1_guard_results hv] at hsg2; have ⟨_, rfl⟩ := Prod.mk.inj hsg2
                    have ⟨_, rfl⟩ := Prod.mk.inj hm2
                    change (_ ∨ _) at r2
                    rcases r2 with ⟨s₃, hs₃, r3⟩ | ⟨he, _⟩
                    · have ⟨_, rfl⟩ := Prod.mk.inj hs₃
                      exact absurd (Prod.mk.inj r3).1 (by intro h; cases h)
                    · exact absurd (Prod.mk.inj he).1 (by intro h; cases h)
                  · exact absurd (Prod.mk.inj he).1 (by intro h; cases h)
                · exact absurd (Prod.mk.inj he).1 (by intro h; cases h)
              · exact absurd (Prod.mk.inj he).1 (by intro h; cases h)
            · exact absurd (Prod.mk.inj he).1 (by intro h; cases h)
        · -- Postchain: 3 guard+modify + modify+throw
          -- Use guard_modify chain + modify_throw_catch for the ending
          -- Structure: seq(gm1)(seq(gm2)(seq(gm3)(seq(modify ret)(throw))))
          -- gm1: guard rb; modify heap[rb].head:=null
          -- gm2: guard rb; modify heap[rb].tail:=null
          -- gm3: guard rb; modify heap[rb].count:=0
          -- Then: modify ret:=removed; throw → error
          -- The error is what gets caught by the outer catch.
          -- Use L1_hoare_seq with match-based postcondition.
          -- For gm1: ok-only, produces rb_after_head
          apply L1_hoare_seq (R := fun s =>
              heapPtrValid s.globals.rawHeap s.locals.rb ∧
              (hVal s.globals.rawHeap s.locals.rb).head = Ptr.null)
          · -- gm1: guard rb; modify head:=null
            intro s₀ hrb
            have h_gm := L1_guard_modify_result
              (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
              (fun s : ProgramState => { s with globals := { s.globals with
                rawHeap := heapUpdate s.globals.rawHeap s.locals.rb
                  ({ hVal s.globals.rawHeap s.locals.rb with head := Ptr.null }) } }) s₀ hrb
            constructor
            · exact h_gm.2
            · intro r s₁ hmem; rw [h_gm.1] at hmem
              have ⟨hr, hs⟩ := Prod.mk.inj hmem; subst hr; subst hs
              constructor
              · exact heapUpdate_preserves_heapPtrValid _ _ _ _ hrb
              · have hb := heapPtrValid_bound hrb
                rw [hVal_heapUpdate_same _ _ _ hb]
          · apply L1_hoare_seq (R := fun s =>
                heapPtrValid s.globals.rawHeap s.locals.rb ∧
                (hVal s.globals.rawHeap s.locals.rb).head = Ptr.null ∧
                (hVal s.globals.rawHeap s.locals.rb).tail = Ptr.null)
            · -- gm2: guard rb; modify tail:=null
              intro s₀ ⟨hrb, h_head⟩
              have h_gm := L1_guard_modify_result
                (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
                (fun s : ProgramState => { s with globals := { s.globals with
                  rawHeap := heapUpdate s.globals.rawHeap s.locals.rb
                    ({ hVal s.globals.rawHeap s.locals.rb with tail := Ptr.null }) } }) s₀ hrb
              constructor
              · exact h_gm.2
              · intro r s₁ hmem; rw [h_gm.1] at hmem
                have ⟨hr, hs⟩ := Prod.mk.inj hmem; subst hr; subst hs
                have hb := heapPtrValid_bound hrb
                have h_eq := hVal_heapUpdate_same _ _ _ hb
                exact ⟨heapUpdate_preserves_heapPtrValid _ _ _ _ hrb,
                       by rw [h_eq]; exact h_head,
                       by rw [h_eq]⟩
            · apply L1_hoare_seq (R := fun s =>
                  heapPtrValid s.globals.rawHeap s.locals.rb ∧
                  (hVal s.globals.rawHeap s.locals.rb).head = Ptr.null ∧
                  (hVal s.globals.rawHeap s.locals.rb).tail = Ptr.null ∧
                  (hVal s.globals.rawHeap s.locals.rb).count = 0)
              · -- gm3: guard rb; modify count:=0
                intro s₀ ⟨hrb, h_head, h_tail⟩
                have h_gm := L1_guard_modify_result
                  (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
                  (fun s : ProgramState => { s with globals := { s.globals with
                    rawHeap := heapUpdate s.globals.rawHeap s.locals.rb
                      ({ hVal s.globals.rawHeap s.locals.rb with count := 0 }) } }) s₀ hrb
                constructor
                · exact h_gm.2
                · intro r s₁ hmem; rw [h_gm.1] at hmem
                  have ⟨hr, hs⟩ := Prod.mk.inj hmem; subst hr; subst hs
                  have hb := heapPtrValid_bound hrb
                  have h_eq := hVal_heapUpdate_same _ _ _ hb
                  exact ⟨heapUpdate_preserves_heapPtrValid _ _ _ _ hrb,
                         by rw [h_eq]; exact h_head,
                         by rw [h_eq]; exact h_tail,
                         by rw [h_eq]⟩
              · -- modify ret:=removed; throw
                intro s₀ ⟨_, h_head, h_tail, h_count⟩
                have h_mt := L1_modify_throw_result
                  (fun s : ProgramState => { s with locals := { s.locals with
                    ret__val := s.locals.removed } }) s₀
                constructor
                · exact h_mt.2
                · intro r s₁ hmem; rw [h_mt.1] at hmem
                  have ⟨hr, hs⟩ := Prod.mk.inj hmem; subst hr; subst hs
                  exact ⟨h_head, h_tail, h_count⟩
  · -- Handler: skip
    intro s ⟨h_head, h_tail, h_count⟩
    constructor
    · intro hf; exact hf
    · intro r s' hmem; have ⟨_, hs⟩ := Prod.mk.inj hmem; subst hs
      intro _; exact ⟨h_head, h_tail, h_count⟩
