-- Proven (sorry-free) validHoare and totalHoare proofs for 7 simple accessors.
-- Split from RBExtFuncSpecs.lean (task 0233).
--
-- validHoare proofs (7):
--   rb_capacity, rb_size, rb_remaining, rb_is_empty, rb_is_full,
--   rb_iter_has_next, rb_stats_total_ops
--
-- totalHoare proofs (7): same 7 functions (no UB)

import Examples.RBExtSpecs

set_option maxHeartbeats 12800000
set_option maxRecDepth 4096

open RingBufferExt

/-! # Projection lemmas for state update -/

-- When we set ret__val, globals and other local fields are preserved.
theorem rb_retval_globals (s : ProgramState) (v : UInt32) :
    ({ s with locals := { s.locals with ret__val := v } } : ProgramState).globals = s.globals := rfl
theorem rb_retval_rb (s : ProgramState) (v : UInt32) :
    ({ s with locals := { s.locals with ret__val := v } } : ProgramState).locals.rb = s.locals.rb := rfl
theorem rb_retval_val (s : ProgramState) (v : UInt32) :
    ({ s with locals := { s.locals with ret__val := v } } : ProgramState).locals.ret__val = v := rfl
theorem rb_retval_stats (s : ProgramState) (v : UInt32) :
    ({ s with locals := { s.locals with ret__val := v } } : ProgramState).locals.stats = s.locals.stats := rfl
theorem rb_retval_iter (s : ProgramState) (v : UInt32) :
    ({ s with locals := { s.locals with ret__val := v } } : ProgramState).locals.iter = s.locals.iter := rfl

/-! # validHoare proofs for 7 simple accessors

    These are the guard-modify-throw-catch-skip pattern (rb_capacity, rb_size, rb_remaining)
    and the conditional pattern (rb_is_empty, rb_is_full, rb_iter_has_next).
    rb_stats_total_ops uses multi-guard pattern. -/

-- rb_capacity: guard heapPtrValid; ret = capacity; throw; catch skip
attribute [local irreducible] hVal heapPtrValid in
theorem rb_capacity_validHoare :
    rb_capacity_spec.satisfiedBy l1_rb_capacity_body := by
  unfold FuncSpec.satisfiedBy rb_capacity_spec validHoare
  intro s hpre
  unfold RingBufferExt.l1_rb_capacity_body
  have h := L1_guard_modify_throw_catch_skip_result
    (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := (hVal s.globals.rawHeap s.locals.rb).capacity } })
    s hpre
  obtain ⟨h_res, h_nf⟩ := h
  constructor
  · exact h_nf
  · intro r s' h_mem
    rw [h_res] at h_mem
    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
    subst hr; subst hs
    intro _
    rw [rb_retval_val, rb_retval_globals, rb_retval_rb]

-- rb_size: guard heapPtrValid; ret = count; throw; catch skip
attribute [local irreducible] hVal heapPtrValid in
theorem rb_size_validHoare :
    rb_size_spec.satisfiedBy l1_rb_size_body := by
  unfold FuncSpec.satisfiedBy rb_size_spec validHoare
  intro s hpre
  unfold RingBufferExt.l1_rb_size_body
  have h := L1_guard_modify_throw_catch_skip_result
    (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := (hVal s.globals.rawHeap s.locals.rb).count } })
    s hpre
  obtain ⟨h_res, h_nf⟩ := h
  constructor
  · exact h_nf
  · intro r s' h_mem
    rw [h_res] at h_mem
    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
    subst hr; subst hs
    intro _
    rw [rb_retval_val, rb_retval_globals, rb_retval_rb]

-- Helper: two-guard + modify + throw + catch skip pattern
-- L1.catch (L1.seq (L1.guard p) (L1.seq (L1.guard q) (L1.seq (L1.modify f) L1.throw))) L1.skip
-- produces {(ok, f s)} and does not fail, when p and q hold.
theorem L1_guard_guard_modify_throw_catch_skip_result
    (p q : ProgramState → Prop) [DecidablePred p] [DecidablePred q]
    (f : ProgramState → ProgramState) (s : ProgramState) (hp : p s) (hq : q s) :
    (L1.catch (L1.seq (L1.guard p) (L1.seq (L1.guard q) (L1.seq (L1.modify f) L1.throw))) L1.skip s).results =
      {(Except.ok (), f s)} ∧
    ¬(L1.catch (L1.seq (L1.guard p) (L1.seq (L1.guard q) (L1.seq (L1.modify f) L1.throw))) L1.skip s).failed := by
  -- Inner chain: seq (guard q) (seq (modify f) throw) at s produces {(error, f s)}
  have h_inner := L1_guard_modify_throw_catch_skip_result q f s hq
  -- But this is for catch pattern. We need the raw inner seq first.
  -- Use composition: guard p gives {(ok, s)}, then the rest.
  have h_mt := L1_modify_throw_result f s
  have h_gmt : (L1.seq (L1.guard q) (L1.seq (L1.modify f) L1.throw) s).results = {(Except.error (), f s)} ∧
               ¬(L1.seq (L1.guard q) (L1.seq (L1.modify f) L1.throw) s).failed := by
    have h_gq := L1_seq_singleton_ok (L1_guard_results hq) (L1_guard_not_failed hq)
      (m₂ := L1.seq (L1.modify f) L1.throw)
    constructor
    · rw [h_gq.1, h_mt.1]
    · intro hf; exact h_mt.2 (h_gq.2.mp hf)
  -- Now: seq (guard p) (inner) at s: guard gives (ok, s), inner gives (error, f s)
  have h_outer := L1_seq_singleton_ok (L1_guard_results hp) (L1_guard_not_failed hp)
    (m₂ := L1.seq (L1.guard q) (L1.seq (L1.modify f) L1.throw))
  have h_body_res : (L1.seq (L1.guard p) (L1.seq (L1.guard q) (L1.seq (L1.modify f) L1.throw)) s).results =
      {(Except.error (), f s)} := by rw [h_outer.1, h_gmt.1]
  have h_body_nf : ¬(L1.seq (L1.guard p) (L1.seq (L1.guard q) (L1.seq (L1.modify f) L1.throw)) s).failed :=
    fun hf => h_gmt.2 (h_outer.2.mp hf)
  exact L1_catch_error_singleton h_body_res h_body_nf

-- rb_remaining: guard heapPtrValid; guard heapPtrValid; ret = capacity - count; throw; catch skip
attribute [local irreducible] hVal heapPtrValid in
theorem rb_remaining_validHoare :
    rb_remaining_spec.satisfiedBy l1_rb_remaining_body := by
  unfold FuncSpec.satisfiedBy rb_remaining_spec validHoare
  intro s hpre
  unfold RingBufferExt.l1_rb_remaining_body
  have h := L1_guard_guard_modify_throw_catch_skip_result
    (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
    (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
    (fun s : ProgramState =>
      { s with locals := { s.locals with ret__val :=
        (hVal s.globals.rawHeap s.locals.rb).capacity - (hVal s.globals.rawHeap s.locals.rb).count } })
    s hpre hpre
  obtain ⟨h_res, h_nf⟩ := h
  constructor
  · exact h_nf
  · intro r s' h_mem
    rw [h_res] at h_mem
    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
    subst hr; subst hs
    intro _
    rw [rb_retval_val, rb_retval_globals, rb_retval_rb]

/-! ## Helper lemmas for conditional return pattern -/

/-- Rewrite catch-seq-condition when condition is true. -/
theorem L1_elim_cond_true
    (c : ProgramState → Bool) {t e m handler : L1Monad ProgramState}
    {s : ProgramState} (h : c s = true) :
    L1.catch (L1.seq (L1.condition c t e) m) handler s =
    L1.catch (L1.seq t m) handler s := by
  unfold L1.catch L1.seq L1.condition; simp [h]

/-- Rewrite catch-seq-condition when condition is false. -/
theorem L1_elim_cond_false
    (c : ProgramState → Bool) {t e m handler : L1Monad ProgramState}
    {s : ProgramState} (h : c s = false) :
    L1.catch (L1.seq (L1.condition c t e) m) handler s =
    L1.catch (L1.seq e m) handler s := by
  unfold L1.catch L1.seq L1.condition; simp [h]

/-- After modify+throw, sequencing with more code still just has error results.
    Combined with catch+skip: catch (seq (seq (modify f) throw) m2) skip s → {(ok, f s)}. -/
theorem L1_modify_throw_seq_catch_skip
    (f : ProgramState → ProgramState) (m2 : L1Monad ProgramState) (s : ProgramState) :
    (L1.catch (L1.seq (L1.seq (L1.modify f) L1.throw) m2) L1.skip s).results =
      {(Except.ok (), f s)} ∧
    ¬(L1.catch (L1.seq (L1.seq (L1.modify f) L1.throw) m2) L1.skip s).failed := by
  have h_mt := L1_modify_throw_result f s
  have h_inner_res : (L1.seq (L1.modify f) L1.throw s).results = {(Except.error (), f s)} := h_mt.1
  have h_inner_nf : ¬(L1.seq (L1.modify f) L1.throw s).failed := h_mt.2
  have h_outer := L1_seq_error_propagate h_inner_res h_inner_nf (m₂ := m2)
  exact L1_catch_error_singleton h_outer.1 h_outer.2

/-! ## Conditional accessor validHoare proofs -/

-- rb_is_empty: catch (seq (cond (count=0) (seq (modify ret=1) throw) skip) (seq (modify ret=0) throw)) skip
attribute [local irreducible] hVal heapPtrValid in
theorem rb_is_empty_validHoare :
    rb_is_empty_spec.satisfiedBy l1_rb_is_empty_body := by
  unfold FuncSpec.satisfiedBy rb_is_empty_spec validHoare
  intro s _
  unfold RingBufferExt.l1_rb_is_empty_body
  by_cases h1 : decide ((hVal s.globals.rawHeap s.locals.rb).count = 0) = true
  · -- count = 0 → ret = 1
    have hcount : (hVal s.globals.rawHeap s.locals.rb).count = 0 := by simpa using h1
    rw [L1_elim_cond_true (fun (st : ProgramState) => decide ((hVal st.globals.rawHeap st.locals.rb).count = 0)) h1]
    have ⟨h_res, h_nf⟩ := L1_modify_throw_seq_catch_skip
      (fun s : ProgramState => { s with locals := { s.locals with ret__val := 1 } })
      (L1.seq (L1.modify (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } })) L1.throw) s
    constructor
    · exact h_nf
    · intro r s' h_mem
      rw [h_res] at h_mem; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_mem
      intro _; constructor
      · intro _; rw [rb_retval_val]
      · intro hne; rw [rb_retval_globals, rb_retval_rb] at hne; exact absurd hcount hne
  · -- count ≠ 0 → skip, then ret = 0
    have hcount : ¬((hVal s.globals.rawHeap s.locals.rb).count = 0) := by simpa using h1
    have h1f : decide ((hVal s.globals.rawHeap s.locals.rb).count = 0) = false := by simpa using h1
    rw [L1_elim_cond_false (fun (st : ProgramState) => decide ((hVal st.globals.rawHeap st.locals.rb).count = 0)) h1f]
    -- After elim_cond_false: catch (seq skip (seq (modify ret=0) throw)) skip s
    have h_skip_res : (L1.skip s).results = {(Except.ok (), s)} := rfl
    have h_skip_nf : ¬(L1.skip s).failed := not_false
    have h_mt := L1_modify_throw_result
      (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } }) s
    have h_body := L1_seq_singleton_ok h_skip_res h_skip_nf
      (m₂ := L1.seq (L1.modify (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } })) L1.throw)
    have h_body_res : (L1.seq L1.skip (L1.seq (L1.modify (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } })) L1.throw) s).results =
        {(Except.error (), { s with locals := { s.locals with ret__val := 0 } })} := by
      rw [h_body.1, h_mt.1]
    have h_body_nf : ¬(L1.seq L1.skip (L1.seq (L1.modify (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } })) L1.throw) s).failed :=
      fun hf => h_mt.2 (h_body.2.mp hf)
    have ⟨h_res, h_nf⟩ := L1_catch_error_singleton h_body_res h_body_nf
    constructor
    · exact h_nf
    · intro r s' h_mem
      rw [h_res] at h_mem; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_mem
      intro _; constructor
      · intro heq; exact absurd heq hcount
      · intro _; rw [rb_retval_val]

-- rb_is_full: catch (seq (cond (count>=capacity) (seq (modify ret=1) throw) skip) (seq (modify ret=0) throw)) skip
attribute [local irreducible] hVal heapPtrValid in
theorem rb_is_full_validHoare :
    rb_is_full_spec.satisfiedBy l1_rb_is_full_body := by
  unfold FuncSpec.satisfiedBy rb_is_full_spec validHoare
  intro s _
  unfold RingBufferExt.l1_rb_is_full_body
  by_cases h1 : decide ((hVal s.globals.rawHeap s.locals.rb).count >= (hVal s.globals.rawHeap s.locals.rb).capacity) = true
  · -- count >= capacity → ret = 1
    have hfull : (hVal s.globals.rawHeap s.locals.rb).count >= (hVal s.globals.rawHeap s.locals.rb).capacity := by simpa using h1
    rw [L1_elim_cond_true (fun (st : ProgramState) => decide ((hVal st.globals.rawHeap st.locals.rb).count >= (hVal st.globals.rawHeap st.locals.rb).capacity)) h1]
    have ⟨h_res, h_nf⟩ := L1_modify_throw_seq_catch_skip
      (fun s : ProgramState => { s with locals := { s.locals with ret__val := 1 } })
      (L1.seq (L1.modify (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } })) L1.throw) s
    constructor
    · exact h_nf
    · intro r s' h_mem
      rw [h_res] at h_mem; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_mem
      intro _; constructor
      · intro _; rw [rb_retval_val]
      · intro hlt; rw [rb_retval_globals, rb_retval_rb] at hlt; exact absurd hfull (Nat.not_le.mpr hlt)
  · -- count < capacity → ret = 0
    have hnotfull : ¬((hVal s.globals.rawHeap s.locals.rb).count >= (hVal s.globals.rawHeap s.locals.rb).capacity) := by simpa using h1
    have h1f : decide ((hVal s.globals.rawHeap s.locals.rb).count >= (hVal s.globals.rawHeap s.locals.rb).capacity) = false := by simpa using h1
    rw [L1_elim_cond_false (fun (st : ProgramState) => decide ((hVal st.globals.rawHeap st.locals.rb).count >= (hVal st.globals.rawHeap st.locals.rb).capacity)) h1f]
    have h_skip_res : (L1.skip s).results = {(Except.ok (), s)} := rfl
    have h_skip_nf : ¬(L1.skip s).failed := not_false
    have h_mt := L1_modify_throw_result
      (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } }) s
    have h_body := L1_seq_singleton_ok h_skip_res h_skip_nf
      (m₂ := L1.seq (L1.modify (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } })) L1.throw)
    have h_body_res : (L1.seq L1.skip (L1.seq (L1.modify (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } })) L1.throw) s).results =
        {(Except.error (), { s with locals := { s.locals with ret__val := 0 } })} := by
      rw [h_body.1, h_mt.1]
    have h_body_nf : ¬(L1.seq L1.skip (L1.seq (L1.modify (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } })) L1.throw) s).failed :=
      fun hf => h_mt.2 (h_body.2.mp hf)
    have ⟨h_res, h_nf⟩ := L1_catch_error_singleton h_body_res h_body_nf
    constructor
    · exact h_nf
    · intro r s' h_mem
      rw [h_res] at h_mem; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_mem
      intro _; constructor
      · intro hge; exact absurd hge hnotfull
      · intro _; rw [rb_retval_val]

-- rb_iter_has_next: catch (seq (cond (current≠null) (seq (modify ret=1) throw) skip) (seq (modify ret=0) throw)) skip
attribute [local irreducible] hVal heapPtrValid in
theorem rb_iter_has_next_validHoare :
    rb_iter_has_next_spec.satisfiedBy l1_rb_iter_has_next_body := by
  unfold FuncSpec.satisfiedBy rb_iter_has_next_spec validHoare
  intro s _
  unfold RingBufferExt.l1_rb_iter_has_next_body
  by_cases h1 : decide ((hVal s.globals.rawHeap s.locals.iter).current ≠ Ptr.null) = true
  · -- current ≠ null → ret = 1
    have hnonnull : (hVal s.globals.rawHeap s.locals.iter).current ≠ Ptr.null := by simpa using h1
    rw [L1_elim_cond_true (fun (st : ProgramState) => decide ((hVal st.globals.rawHeap st.locals.iter).current ≠ Ptr.null)) h1]
    have ⟨h_res, h_nf⟩ := L1_modify_throw_seq_catch_skip
      (fun s : ProgramState => { s with locals := { s.locals with ret__val := 1 } })
      (L1.seq (L1.modify (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } })) L1.throw) s
    constructor
    · exact h_nf
    · intro r s' h_mem
      rw [h_res] at h_mem; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_mem
      intro _; constructor
      · intro _; rw [rb_retval_val]
      · intro hnull; rw [rb_retval_globals, rb_retval_iter] at hnull; exact absurd hnull hnonnull
  · -- current = null → ret = 0
    have hnull : ¬((hVal s.globals.rawHeap s.locals.iter).current ≠ Ptr.null) := by simpa using h1
    have h1f : decide ((hVal s.globals.rawHeap s.locals.iter).current ≠ Ptr.null) = false := by simpa using h1
    rw [L1_elim_cond_false (fun (st : ProgramState) => decide ((hVal st.globals.rawHeap st.locals.iter).current ≠ Ptr.null)) h1f]
    have h_skip_res : (L1.skip s).results = {(Except.ok (), s)} := rfl
    have h_skip_nf : ¬(L1.skip s).failed := not_false
    have h_mt := L1_modify_throw_result
      (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } }) s
    have h_body := L1_seq_singleton_ok h_skip_res h_skip_nf
      (m₂ := L1.seq (L1.modify (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } })) L1.throw)
    have h_body_res : (L1.seq L1.skip (L1.seq (L1.modify (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } })) L1.throw) s).results =
        {(Except.error (), { s with locals := { s.locals with ret__val := 0 } })} := by
      rw [h_body.1, h_mt.1]
    have h_body_nf : ¬(L1.seq L1.skip (L1.seq (L1.modify (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } })) L1.throw) s).failed :=
      fun hf => h_mt.2 (h_body.2.mp hf)
    have ⟨h_res, h_nf⟩ := L1_catch_error_singleton h_body_res h_body_nf
    constructor
    · exact h_nf
    · intro r s' h_mem
      rw [h_res] at h_mem; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_mem
      intro _; constructor
      · intro hne; exact absurd hne hnull
      · intro _; rw [rb_retval_val]

-- rb_stats_total_ops has 4 identical guards. Build the chain by composing L1_seq_singleton_ok.
theorem L1_4guard_modify_throw_catch_skip_result
    (p : ProgramState → Prop) [DecidablePred p]
    (f : ProgramState → ProgramState) (s : ProgramState) (hp : p s) :
    (L1.catch
      (L1.seq (L1.guard p)
        (L1.seq (L1.guard p)
          (L1.seq (L1.guard p)
            (L1.seq (L1.guard p)
              (L1.seq (L1.modify f) L1.throw)))))
      L1.skip s).results = {(Except.ok (), f s)} ∧
    ¬(L1.catch
      (L1.seq (L1.guard p)
        (L1.seq (L1.guard p)
          (L1.seq (L1.guard p)
            (L1.seq (L1.guard p)
              (L1.seq (L1.modify f) L1.throw)))))
      L1.skip s).failed := by
  -- Peel guards one by one using L1_seq_singleton_ok
  have h_mt := L1_modify_throw_result f s
  -- innermost: seq (guard p) (seq (modify f) throw) -> {(error, f s)}
  have h_g4 := L1_seq_singleton_ok (L1_guard_results hp) (L1_guard_not_failed hp)
    (m₂ := L1.seq (L1.modify f) L1.throw)
  have h4_res : (L1.seq (L1.guard p) (L1.seq (L1.modify f) L1.throw) s).results =
      {(Except.error (), f s)} := by rw [h_g4.1, h_mt.1]
  have h4_nf : ¬(L1.seq (L1.guard p) (L1.seq (L1.modify f) L1.throw) s).failed :=
    fun hf => h_mt.2 (h_g4.2.mp hf)
  -- next guard
  have h_g3 := L1_seq_singleton_ok (L1_guard_results hp) (L1_guard_not_failed hp)
    (m₂ := L1.seq (L1.guard p) (L1.seq (L1.modify f) L1.throw))
  have h3_res : (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.seq (L1.modify f) L1.throw)) s).results =
      {(Except.error (), f s)} := by rw [h_g3.1, h4_res]
  have h3_nf : ¬(L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.seq (L1.modify f) L1.throw)) s).failed :=
    fun hf => h4_nf (h_g3.2.mp hf)
  -- next guard
  have h_g2 := L1_seq_singleton_ok (L1_guard_results hp) (L1_guard_not_failed hp)
    (m₂ := L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.seq (L1.modify f) L1.throw)))
  have h2_res : (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.seq (L1.modify f) L1.throw))) s).results =
      {(Except.error (), f s)} := by rw [h_g2.1, h3_res]
  have h2_nf : ¬(L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.seq (L1.modify f) L1.throw))) s).failed :=
    fun hf => h3_nf (h_g2.2.mp hf)
  -- outermost guard
  have h_g1 := L1_seq_singleton_ok (L1_guard_results hp) (L1_guard_not_failed hp)
    (m₂ := L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.seq (L1.modify f) L1.throw))))
  have h1_res : (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.seq (L1.modify f) L1.throw)))) s).results =
      {(Except.error (), f s)} := by rw [h_g1.1, h2_res]
  have h1_nf : ¬(L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.seq (L1.modify f) L1.throw)))) s).failed :=
    fun hf => h2_nf (h_g1.2.mp hf)
  exact L1_catch_error_singleton h1_res h1_nf

attribute [local irreducible] hVal heapPtrValid in
theorem rb_stats_total_ops_validHoare :
    rb_stats_total_ops_spec.satisfiedBy l1_rb_stats_total_ops_body := by
  unfold FuncSpec.satisfiedBy rb_stats_total_ops_spec validHoare
  intro s hpre
  unfold RingBufferExt.l1_rb_stats_total_ops_body
  have h := L1_4guard_modify_throw_catch_skip_result
    (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.stats)
    (fun s : ProgramState => { s with locals := { s.locals with ret__val :=
      (((hVal s.globals.rawHeap s.locals.stats).total_pushes +
        (hVal s.globals.rawHeap s.locals.stats).total_pops) +
        (hVal s.globals.rawHeap s.locals.stats).push_failures) +
        (hVal s.globals.rawHeap s.locals.stats).pop_failures } })
    s hpre
  obtain ⟨h_res, h_nf⟩ := h
  constructor
  · exact h_nf
  · intro r s' h_mem
    rw [h_res] at h_mem
    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
    subst hr; subst hs
    intro _
    rw [rb_retval_val, rb_retval_globals, rb_retval_stats]

/-! # Task 0139: totalHoare for UB-freedom

    State totalHoare (not just validHoare) for the 7 loop-free functions that
    already have Terminates proofs (TerminationProofs.lean).
    totalHoare = validHoare + terminates = no UB possible.

    The 7 functions: rb_capacity, rb_size, rb_remaining, rb_is_empty,
    rb_is_full, rb_stats_total_ops, rb_iter_has_next -/

/-- totalHoare for rb_capacity: no UB (all guards discharged + terminates).
    Proven: validHoare from rb_capacity_validHoare + termination is trivial
    (guard-modify-throw-catch-skip always produces exactly one result). -/
theorem rb_capacity_totalHoare :
    totalHoare rb_capacity_spec.pre l1_rb_capacity_body rb_capacity_spec.post := by
  constructor
  · exact rb_capacity_validHoare
  · -- termination: the L1 body always produces at least one result
    intro s₀ hpre
    unfold l1_rb_capacity_body
    have h := L1_guard_modify_throw_catch_skip_result
      (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
      (fun s : ProgramState => { s with locals := { s.locals with ret__val := (hVal s.globals.rawHeap s.locals.rb).capacity } })
      s₀ hpre
    exact ⟨_, _, by rw [h.1]; rfl⟩

/-- totalHoare for rb_size: no UB. -/
theorem rb_size_totalHoare :
    totalHoare rb_size_spec.pre l1_rb_size_body rb_size_spec.post := by
  constructor
  · exact rb_size_validHoare
  · intro s₀ hpre
    unfold l1_rb_size_body
    have h := L1_guard_modify_throw_catch_skip_result
      (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
      (fun s : ProgramState => { s with locals := { s.locals with ret__val := (hVal s.globals.rawHeap s.locals.rb).count } })
      s₀ hpre
    exact ⟨_, _, by rw [h.1]; rfl⟩

/-- totalHoare for rb_remaining: no UB. -/
theorem rb_remaining_totalHoare :
    totalHoare rb_remaining_spec.pre l1_rb_remaining_body rb_remaining_spec.post := by
  constructor
  · exact rb_remaining_validHoare
  · intro s₀ hpre
    unfold l1_rb_remaining_body
    have h := L1_guard_guard_modify_throw_catch_skip_result
      (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
      (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
      (fun s : ProgramState =>
        { s with locals := { s.locals with ret__val :=
          (hVal s.globals.rawHeap s.locals.rb).capacity - (hVal s.globals.rawHeap s.locals.rb).count } })
      s₀ hpre hpre
    exact ⟨_, _, by rw [h.1]; rfl⟩

/-- totalHoare for rb_is_empty: no UB. -/
theorem rb_is_empty_totalHoare :
    totalHoare rb_is_empty_spec.pre l1_rb_is_empty_body rb_is_empty_spec.post := by
  constructor
  · exact rb_is_empty_validHoare
  · intro s₀ _
    unfold l1_rb_is_empty_body
    by_cases h1 : decide ((hVal s₀.globals.rawHeap s₀.locals.rb).count = 0) = true
    · rw [L1_elim_cond_true (fun (st : ProgramState) => decide ((hVal st.globals.rawHeap st.locals.rb).count = 0)) h1]
      have ⟨h_res, _⟩ := L1_modify_throw_seq_catch_skip
        (fun s : ProgramState => { s with locals := { s.locals with ret__val := 1 } })
        (L1.seq (L1.modify (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } })) L1.throw) s₀
      exact ⟨_, _, by rw [h_res]; rfl⟩
    · have h1f : decide ((hVal s₀.globals.rawHeap s₀.locals.rb).count = 0) = false := by simpa using h1
      rw [L1_elim_cond_false (fun (st : ProgramState) => decide ((hVal st.globals.rawHeap st.locals.rb).count = 0)) h1f]
      have h_mt := L1_modify_throw_result
        (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } }) s₀
      have h_body := L1_seq_singleton_ok (show (L1.skip s₀).results = {(Except.ok (), s₀)} from rfl) not_false
        (m₂ := L1.seq (L1.modify (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } })) L1.throw)
      have h_body_res : (L1.seq L1.skip (L1.seq (L1.modify (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } })) L1.throw) s₀).results =
          {(Except.error (), { s₀ with locals := { s₀.locals with ret__val := 0 } })} := by
        rw [h_body.1, h_mt.1]
      have h_body_nf : ¬(L1.seq L1.skip (L1.seq (L1.modify (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } })) L1.throw) s₀).failed :=
        fun hf => h_mt.2 (h_body.2.mp hf)
      have ⟨h_res, _⟩ := L1_catch_error_singleton h_body_res h_body_nf
      exact ⟨_, _, by rw [h_res]; rfl⟩

/-- totalHoare for rb_is_full: no UB. -/
theorem rb_is_full_totalHoare :
    totalHoare rb_is_full_spec.pre l1_rb_is_full_body rb_is_full_spec.post := by
  constructor
  · exact rb_is_full_validHoare
  · intro s₀ _
    unfold l1_rb_is_full_body
    by_cases h1 : decide ((hVal s₀.globals.rawHeap s₀.locals.rb).count >= (hVal s₀.globals.rawHeap s₀.locals.rb).capacity) = true
    · rw [L1_elim_cond_true (fun (st : ProgramState) => decide ((hVal st.globals.rawHeap st.locals.rb).count >= (hVal st.globals.rawHeap st.locals.rb).capacity)) h1]
      have ⟨h_res, _⟩ := L1_modify_throw_seq_catch_skip
        (fun s : ProgramState => { s with locals := { s.locals with ret__val := 1 } })
        (L1.seq (L1.modify (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } })) L1.throw) s₀
      exact ⟨_, _, by rw [h_res]; rfl⟩
    · have h1f : decide ((hVal s₀.globals.rawHeap s₀.locals.rb).count >= (hVal s₀.globals.rawHeap s₀.locals.rb).capacity) = false := by simpa using h1
      rw [L1_elim_cond_false (fun (st : ProgramState) => decide ((hVal st.globals.rawHeap st.locals.rb).count >= (hVal st.globals.rawHeap st.locals.rb).capacity)) h1f]
      have h_mt := L1_modify_throw_result
        (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } }) s₀
      have h_body := L1_seq_singleton_ok (show (L1.skip s₀).results = {(Except.ok (), s₀)} from rfl) not_false
        (m₂ := L1.seq (L1.modify (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } })) L1.throw)
      have h_body_res : (L1.seq L1.skip (L1.seq (L1.modify (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } })) L1.throw) s₀).results =
          {(Except.error (), { s₀ with locals := { s₀.locals with ret__val := 0 } })} := by
        rw [h_body.1, h_mt.1]
      have h_body_nf : ¬(L1.seq L1.skip (L1.seq (L1.modify (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } })) L1.throw) s₀).failed :=
        fun hf => h_mt.2 (h_body.2.mp hf)
      have ⟨h_res, _⟩ := L1_catch_error_singleton h_body_res h_body_nf
      exact ⟨_, _, by rw [h_res]; rfl⟩

/-- totalHoare for rb_stats_total_ops: no UB. -/
theorem rb_stats_total_ops_totalHoare :
    totalHoare rb_stats_total_ops_spec.pre l1_rb_stats_total_ops_body rb_stats_total_ops_spec.post := by
  constructor
  · exact rb_stats_total_ops_validHoare
  · intro s₀ hpre
    unfold l1_rb_stats_total_ops_body
    have h := L1_4guard_modify_throw_catch_skip_result
      (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.stats)
      (fun s : ProgramState => { s with locals := { s.locals with ret__val :=
        (((hVal s.globals.rawHeap s.locals.stats).total_pushes +
          (hVal s.globals.rawHeap s.locals.stats).total_pops) +
          (hVal s.globals.rawHeap s.locals.stats).push_failures) +
          (hVal s.globals.rawHeap s.locals.stats).pop_failures } })
      s₀ hpre
    exact ⟨_, _, by rw [h.1]; rfl⟩

/-- totalHoare for rb_iter_has_next: no UB. -/
theorem rb_iter_has_next_totalHoare :
    totalHoare rb_iter_has_next_spec.pre l1_rb_iter_has_next_body rb_iter_has_next_spec.post := by
  constructor
  · exact rb_iter_has_next_validHoare
  · intro s₀ _
    unfold l1_rb_iter_has_next_body
    by_cases h1 : decide ((hVal s₀.globals.rawHeap s₀.locals.iter).current ≠ Ptr.null) = true
    · rw [L1_elim_cond_true (fun (st : ProgramState) => decide ((hVal st.globals.rawHeap st.locals.iter).current ≠ Ptr.null)) h1]
      have ⟨h_res, _⟩ := L1_modify_throw_seq_catch_skip
        (fun s : ProgramState => { s with locals := { s.locals with ret__val := 1 } })
        (L1.seq (L1.modify (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } })) L1.throw) s₀
      exact ⟨_, _, by rw [h_res]; rfl⟩
    · have h1f : decide ((hVal s₀.globals.rawHeap s₀.locals.iter).current ≠ Ptr.null) = false := by simpa using h1
      rw [L1_elim_cond_false (fun (st : ProgramState) => decide ((hVal st.globals.rawHeap st.locals.iter).current ≠ Ptr.null)) h1f]
      have h_mt := L1_modify_throw_result
        (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } }) s₀
      have h_body := L1_seq_singleton_ok (show (L1.skip s₀).results = {(Except.ok (), s₀)} from rfl) not_false
        (m₂ := L1.seq (L1.modify (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } })) L1.throw)
      have h_body_res : (L1.seq L1.skip (L1.seq (L1.modify (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } })) L1.throw) s₀).results =
          {(Except.error (), { s₀ with locals := { s₀.locals with ret__val := 0 } })} := by
        rw [h_body.1, h_mt.1]
      have h_body_nf : ¬(L1.seq L1.skip (L1.seq (L1.modify (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } })) L1.throw) s₀).failed :=
        fun hf => h_mt.2 (h_body.2.mp hf)
      have ⟨h_res, _⟩ := L1_catch_error_singleton h_body_res h_body_nf
      exact ⟨_, _, by rw [h_res]; rfl⟩
