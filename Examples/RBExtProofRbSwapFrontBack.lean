-- Proof for rb_swap_front_back_validHoare (split from RBExtProofsSorry for memory)
import Examples.RBExtSpecs
set_option maxHeartbeats 51200000
set_option maxRecDepth 8192
open RingBufferExt

/-! # Step functions with anonymous constructors (avoiding kernel depth)

  Locals fields (46) in order:
    a, actual, b, ca, cap, cb, count, cur, current_count, delta,
    dst, filled, front, idx, iter, max_drain, max_val, min_val, modified, n,
    new_val, node, nxt, old_head, old_val, out_val, pop_ok, pop_result, prev,
    push_ok, push_result, rb, removed, replaced, result, ret__val,
    scratch, skipped, src, stats, temp_node, threshold, tmp, total, transferred, val
-/

-- Step A: tmp := (hVal heap head).value (locals-only)
private noncomputable def swap_set_tmp (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold,
    (hVal s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head).value,
    s.locals.total, s.locals.transferred, s.locals.val⟩⟩

-- Step B: head.value := tail.value (heap-only)
private noncomputable def swap_head_val (s : ProgramState) : ProgramState :=
  ⟨⟨heapUpdate s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head
    ({ hVal s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head with
       value := (hVal s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).tail).value })⟩,
   s.locals⟩

-- Step C: tail.value := tmp (heap-only)
private noncomputable def swap_tail_val (s : ProgramState) : ProgramState :=
  ⟨⟨heapUpdate s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).tail
    ({ hVal s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).tail with
       value := s.locals.tmp })⟩,
   s.locals⟩

-- Step D: ret__val := 0 (locals-only)
private noncomputable def swap_set_ret0 (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, 0,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

-- Dead branches: ret__val := 1 (locals-only)
private noncomputable def swap_set_ret1 (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, 1,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

/-! # Funext lemmas -/

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem swap_set_tmp_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      tmp := (hVal s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head).value } }) =
    swap_set_tmp := by funext s; unfold swap_set_tmp; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem swap_head_val_funext :
    (fun s : ProgramState => { s with globals := { s.globals with
      rawHeap := heapUpdate s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head
        ({ hVal s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head with
           value := (hVal s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).tail).value }) } }) =
    swap_head_val := by funext s; unfold swap_head_val; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem swap_tail_val_funext :
    (fun s : ProgramState => { s with globals := { s.globals with
      rawHeap := heapUpdate s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).tail
        ({ hVal s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).tail with
           value := s.locals.tmp }) } }) =
    swap_tail_val := by funext s; unfold swap_tail_val; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem swap_set_ret0_funext :
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } }) =
    swap_set_ret0 := by funext s; unfold swap_set_ret0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem swap_set_ret1_funext :
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := 1 } }) =
    swap_set_ret1 := by funext s; unfold swap_set_ret1; rfl

/-! # Projection lemmas -/

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem swap_set_tmp_globals (s : ProgramState) :
    (swap_set_tmp s).globals = s.globals := by unfold swap_set_tmp; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem swap_set_tmp_rb (s : ProgramState) :
    (swap_set_tmp s).locals.rb = s.locals.rb := by unfold swap_set_tmp; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem swap_head_val_locals (s : ProgramState) :
    (swap_head_val s).locals = s.locals := by unfold swap_head_val; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem swap_tail_val_locals (s : ProgramState) :
    (swap_tail_val s).locals = s.locals := by unfold swap_tail_val; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem swap_set_ret0_globals (s : ProgramState) :
    (swap_set_ret0 s).globals = s.globals := by unfold swap_set_ret0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem swap_set_ret0_ret (s : ProgramState) :
    (swap_set_ret0 s).locals.ret__val = 0 := by unfold swap_set_ret0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem swap_set_ret1_globals (s : ProgramState) :
    (swap_set_ret1 s).globals = s.globals := by unfold swap_set_ret1; rfl

/-! # Main theorem -/

set_option maxRecDepth 16384 in
set_option maxHeartbeats 102400000 in
attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem rb_swap_front_back_validHoare :
    rb_swap_front_back_spec.satisfiedBy RingBufferExt.l1_rb_swap_front_back_body := by
  unfold FuncSpec.satisfiedBy rb_swap_front_back_spec
  unfold RingBufferExt.l1_rb_swap_front_back_body
  -- Rewrite all locals-only modify functions with anonymous-constructor step functions
  simp only [swap_set_tmp_funext, swap_head_val_funext, swap_tail_val_funext,
    swap_set_ret0_funext, swap_set_ret1_funext]
  -- Outer: catch(body, skip). Body ends with throw, handler is skip.
  apply L1_hoare_catch (R := fun s => s.locals.ret__val = 0)
  · -- Body: seq(cond1, seq(cond2, seq(cond3, chain)))
    -- All 3 conditions dead (false = skip), chain = A;B;C;D ending in throw.

    -- Peel off cond1: count < 2 (dead since count ≥ 2)
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

    · -- Peel off cond2: head = null (dead since head ≠ null)
      apply L1_hoare_seq (R := fun s =>
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

      · -- Peel off cond3: tail = null (dead since tail ≠ null)
        apply L1_hoare_seq (R := fun s =>
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
          -- A = guard(headV); swap_set_tmp  [locals only]
          -- B = guard(headV); guard(tailV); swap_head_val  [heap]
          -- C = guard(tailV); swap_tail_val  [heap]
          -- D = swap_set_ret0; throw

          -- Step A: guard(headValid); swap_set_tmp
          apply L1_hoare_seq_ok (R := fun s =>
            heapPtrValid s.globals.rawHeap s.locals.rb ∧
            heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head ∧
            heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).tail)
          · apply L1_hoare_guard_modify_fused
            · intro s ⟨_, hhv, _⟩; exact hhv
            · intro s ⟨hrb, hhv, htv⟩; constructor; · rfl
              rw [swap_set_tmp_globals, swap_set_tmp_rb]
              exact ⟨hrb, hhv, htv⟩

          · -- seq(B, seq(C, D))
            -- Step B: guard(headV); guard(tailV); swap_head_val
            apply L1_hoare_seq_ok (R := fun s =>
              heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).tail)
            · -- B: split guard(headV) from seq(guard(tailV), swap_head_val)
              apply L1_hoare_seq_ok (R := fun s =>
                heapPtrValid s.globals.rawHeap s.locals.rb ∧
                heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head ∧
                heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).tail)
              · -- guard(headValid)
                apply L1_hoare_pre (P := fun s =>
                  (heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head) ∧
                  (heapPtrValid s.globals.rawHeap s.locals.rb ∧
                   heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head ∧
                   heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).tail))
                · intro s ⟨hrb, hhv, htv⟩; exact ⟨hhv, hrb, hhv, htv⟩
                · exact L1_hoare_guard' _ _
              · -- guard(tailValid); swap_head_val
                apply L1_hoare_guard_modify_fused
                · intro s ⟨_, _, htv⟩; exact htv
                · intro s ⟨hrb, hhv, htv⟩; constructor; · rfl
                  -- After heapUpdate at head, need (hVal newHeap rb).tail valid
                  rw [swap_head_val_locals]
                  have h_disj := ptrDisjoint_symm (rb_node_disjoint hrb hhv)
                  show heapPtrValid (swap_head_val s).globals.rawHeap
                    (hVal (swap_head_val s).globals.rawHeap s.locals.rb).tail
                  unfold swap_head_val
                  simp only []
                  rw [hVal_heapUpdate_disjoint _ _ _ _ (heapPtrValid_bound hhv)
                      (heapPtrValid_bound hrb) h_disj]
                  exact heapUpdate_preserves_heapPtrValid _ _ _ _ htv

            · -- seq(C, D)
              apply L1_hoare_seq_ok (R := fun _ => True)
              · -- Step C: guard(tailValid); swap_tail_val
                apply L1_hoare_guard_modify_fused
                · intro s htv; exact htv
                · intro s _; constructor; · rfl; exact trivial
              · -- Step D: swap_set_ret0; throw
                apply L1_hoare_modify_throw_catch
                intro s _; rw [swap_set_ret0_ret]

  · -- Handler: skip converts error → ok, postcondition is trivial
    intro s hret
    constructor
    · intro hf; exact hf
    · intro r s' hmem
      have ⟨hr, hs⟩ := Prod.mk.inj hmem; subst hr; subst hs
      intro _; exact ⟨hret, rfl, rfl, rfl, rfl⟩
