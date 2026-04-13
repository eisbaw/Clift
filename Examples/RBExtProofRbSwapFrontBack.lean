-- Proof for rb_swap_front_back_validHoare (split from RBExtProofsSorry for memory)
import Examples.RBExtSpecs
set_option maxHeartbeats 51200000
set_option maxRecDepth 8192
open RingBufferExt

/-! # Step function for tmp := hVal(...) (avoiding kernel depth on 46-field Locals) -/

private noncomputable def set_tmp (v : UInt32) (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, v,
    s.locals.total, s.locals.transferred, s.locals.val⟩⟩

@[simp] private theorem set_tmp_globals (v : UInt32) (s : ProgramState) :
    (set_tmp v s).globals = s.globals := by unfold set_tmp; rfl
@[simp] private theorem set_tmp_rb (v : UInt32) (s : ProgramState) :
    (set_tmp v s).locals.rb = s.locals.rb := by unfold set_tmp; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem set_tmp_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      tmp := (hVal s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head).value } }) =
    (fun s => set_tmp ((hVal s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head).value) s) := by
  funext s; unfold set_tmp; rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 204800000 in
attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem rb_swap_front_back_validHoare :
    rb_swap_front_back_spec.satisfiedBy RingBufferExt.l1_rb_swap_front_back_body := by
  unfold FuncSpec.satisfiedBy rb_swap_front_back_spec
  apply L1_hoare_catch (R := fun s => s.locals.ret__val = 0)
  · -- Body: seq(cond1, seq(cond2, seq(cond3, chain)))
    apply L1_hoare_seq (R := fun s =>
      heapPtrValid s.globals.rawHeap s.locals.rb ∧
      (hVal s.globals.rawHeap s.locals.rb).head ≠ Ptr.null ∧
      (hVal s.globals.rawHeap s.locals.rb).tail ≠ Ptr.null ∧
      heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head ∧
      heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).tail)
    · apply L1_hoare_condition
      · intro s ⟨⟨_, hge, _, _, _, _⟩, hcond⟩
        simp only [decide_eq_true_eq] at hcond
        exact absurd hcond (Nat.not_lt.mpr hge)
      · intro s ⟨⟨hrb, _, hhn, htn, hhv, htv⟩, _⟩
        constructor
        · intro hf; exact hf
        · intro r s' hmem
          have ⟨hr, hs⟩ := Prod.mk.inj hmem; subst hr; subst hs
          exact ⟨hrb, hhn, htn, hhv, htv⟩
    · apply L1_hoare_seq (R := fun s =>
        heapPtrValid s.globals.rawHeap s.locals.rb ∧
        (hVal s.globals.rawHeap s.locals.rb).head ≠ Ptr.null ∧
        (hVal s.globals.rawHeap s.locals.rb).tail ≠ Ptr.null ∧
        heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head ∧
        heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).tail)
      · apply L1_hoare_condition
        · intro s ⟨⟨_, hhn, _, _, _⟩, hcond⟩
          simp only [decide_eq_true_eq] at hcond
          exact absurd hcond hhn
        · intro s ⟨hpre, _⟩
          constructor
          · intro hf; exact hf
          · intro r s' hmem
            have ⟨hr, hs⟩ := Prod.mk.inj hmem; subst hr; subst hs
            exact hpre
      · apply L1_hoare_seq (R := fun s =>
          heapPtrValid s.globals.rawHeap s.locals.rb ∧
          heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head ∧
          heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).tail)
        · apply L1_hoare_condition
          · intro s ⟨⟨_, _, htn, _, _⟩, hcond⟩
            simp only [decide_eq_true_eq] at hcond
            exact absurd hcond htn
          · intro s ⟨⟨hrb, _, _, hhv, htv⟩, _⟩
            constructor
            · intro hf; exact hf
            · intro r s' hmem
              have ⟨hr, hs⟩ := Prod.mk.inj hmem; subst hr; subst hs
              exact ⟨hrb, hhv, htv⟩
        · -- Chain: seq(A, seq(B, seq(C, D)))
          -- Step A: guard(headV); modify(tmp := head.val) -- rewrite to set_tmp
          apply L1_hoare_seq_ok (R := fun s =>
            heapPtrValid s.globals.rawHeap s.locals.rb ∧
            heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head ∧
            heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).tail)
          · rw [show (fun s : ProgramState => { s with locals := { s.locals with
                tmp := (hVal s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head).value } }) =
                (fun s => set_tmp ((hVal s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head).value) s)
                from set_tmp_funext]
            apply L1_hoare_guard_modify_fused
            · intro s ⟨_, hhv, _⟩; exact hhv
            · intro s ⟨hrb, hhv, htv⟩
              constructor; · rfl
              simp only [set_tmp_globals, set_tmp_rb]
              exact ⟨hrb, hhv, htv⟩
          · -- Step B: guard(headV); guard(tailV); modify(head.val := tail.val)
            apply L1_hoare_seq_ok (R := fun s =>
              heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).tail)
            · apply L1_hoare_seq_ok (R := fun s =>
                heapPtrValid s.globals.rawHeap s.locals.rb ∧
                heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head ∧
                heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).tail)
              · apply L1_hoare_pre (P := fun s =>
                  (heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head) ∧
                  (heapPtrValid s.globals.rawHeap s.locals.rb ∧
                   heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head ∧
                   heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).tail))
                · intro s ⟨hrb, hhv, htv⟩; exact ⟨hhv, hrb, hhv, htv⟩
                · exact L1_hoare_guard' _ _
              · apply L1_hoare_guard_modify_fused
                · intro s ⟨_, _, htv⟩; exact htv
                · intro s ⟨hrb, hhv, htv⟩; dsimp only; constructor; · rfl
                  have h_disj := ptrDisjoint_symm (rb_node_disjoint hrb hhv)
                  rw [hVal_heapUpdate_disjoint _ _ _ _ (heapPtrValid_bound hhv)
                      (heapPtrValid_bound hrb) h_disj]
                  exact heapUpdate_preserves_heapPtrValid _ _ _ _ htv
            · -- Step C: guard(tailV); modify(tail.val := tmp) + Step D: modify(ret:=0); throw
              apply L1_hoare_seq_ok (R := fun _ => True)
              · apply L1_hoare_guard_modify_fused
                · intro s htv; exact htv
                · intro s _; dsimp only; exact ⟨rfl, trivial⟩
              · apply L1_hoare_modify_throw_catch
                intro s _; dsimp only
  · -- Handler: skip
    intro s hret
    constructor
    · intro hf; exact hf
    · intro r s' hmem
      have ⟨hr, hs⟩ := Prod.mk.inj hmem; subst hr; subst hs
      intro _; exact ⟨hret, rfl, rfl, rfl, rfl⟩
