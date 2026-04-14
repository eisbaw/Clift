-- Phase 3a: swap correctness proof — first pointer verification test
--
-- Proves: after swap(&a, &b), *a and *b are exchanged.
-- Pipeline: swap.c -> CImporter -> CSimpl (Generated/Swap.lean)
--           -> L1 lifting -> L1corres_cHoare_bridge

import Generated.Swap
import Clift.Lifting.Pipeline
import Clift.Lifting.L1HoareRules
import Clift.MonadLib.HoareRules

set_option maxHeartbeats 12800000
set_option maxRecDepth 16384

/-! # Auto-generate L1 body + L1corres via clift -/

clift Swap

open Swap

/-! # Step function decomposition for validHoare proofs

    Uses explicit constructors (CState.mk, Globals.mk, Locals.mk) instead of
    { s with ... } to avoid deep kernel term nesting from structure update
    desugaring. This is critical for kernel-checkable proofs. -/

/-- Step 1 transform: t := *a (explicit constructor, no have/let bindings) -/
private noncomputable def swap_f1 (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.b, hVal s.globals.rawHeap s.locals.a⟩⟩

/-- Step 2 transform: *a := *b (explicit constructor, no have/let bindings) -/
private noncomputable def swap_f2 (s : ProgramState) : ProgramState :=
  ⟨⟨heapUpdate s.globals.rawHeap s.locals.a (hVal s.globals.rawHeap s.locals.b)⟩, s.locals⟩

/-- Step 3 transform: *b := t (explicit constructor, no have/let bindings) -/
private noncomputable def swap_f3 (s : ProgramState) : ProgramState :=
  ⟨⟨heapUpdate s.globals.rawHeap s.locals.b s.locals.t⟩, s.locals⟩

/-- Step 1 as L1 monad: guard(ptrValid a) >> modify(swap_f1) -/
private noncomputable def swap_l1_step1 : L1Monad ProgramState :=
  L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.a)) (L1.modify swap_f1)

/-- Step 2: guard(ptrValid a) >> guard(ptrValid b) >> modify(swap_f2) -/
private noncomputable def swap_l1_step2 : L1Monad ProgramState :=
  L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.a))
    (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.b)) (L1.modify swap_f2))

/-- Step 3: guard(ptrValid b) >> modify(swap_f3) -/
private noncomputable def swap_l1_step3 : L1Monad ProgramState :=
  L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.b)) (L1.modify swap_f3)

/-- The swap body decomposed into named steps.
    Proven equal to the clift-generated Swap.l1_swap_body. -/
private noncomputable abbrev swap_body_decomposed : L1Monad ProgramState :=
  L1.catch (L1.seq swap_l1_step1 (L1.seq swap_l1_step2 swap_l1_step3)) L1.skip

private theorem swap_body_decomposed_eq :
    swap_body_decomposed = Swap.l1_swap_body := by
  unfold swap_body_decomposed swap_l1_step1 swap_l1_step2 swap_l1_step3 Swap.l1_swap_body
  rfl

/-! # validHoare for swap

    Proof strategy: decompose the computation into individual steps, each
    proved as a separate lemma with explicit intermediate states. This keeps
    proof terms at a fixed depth, avoiding Lean 4 kernel deep recursion.

    The computation trace (when all guards hold):
      s0 (initial) ->
      s1 = {s0 with t := *a}     (guard ptrValid_a, modify t := *a)
      s2 = {s1 with *a := *b}    (guard ptrValid_a, guard ptrValid_b, modify *a := *b)
      s3 = {s2 with *b := t}     (guard ptrValid_b, modify *b := t)
    Final: catch produces s3, postcondition holds by heap update lemmas.

    The key insight: swap_body_decomposed is defined using L1 combinators (guard, modify,
    seq, catch). We unfold it directly and work with the L1 combinator definitions,
    avoiding any intermediate abbrevs that would create kernel checking depth. -/

/-! ## Projection lemmas for swap_f1, swap_f2, swap_f3

Strategy to avoid kernel deep recursion:
- First-level projections (.globals, .locals) use `show` to expand swap_fN
  to its anonymous constructor, then `rfl`. With hVal/heapUpdate irreducible,
  the kernel checks a single iota reduction without unfolding hVal internals.
- Second-level projections (.locals.a, .globals.rawHeap) use `rw` with the
  first-level lemma, reducing the double iota to a single iota step.
-/

-- swap_f1: ⟨s.globals, ⟨s.locals.a, s.locals.b, hVal s.globals.rawHeap s.locals.a⟩⟩
attribute [local irreducible] hVal in
@[simp] private theorem swap_f1_globals (s : ProgramState) :
    (swap_f1 s).globals = s.globals := by
  show (⟨s.globals, ⟨s.locals.a, s.locals.b, hVal s.globals.rawHeap s.locals.a⟩⟩ :
    ProgramState).globals = _; rfl

attribute [local irreducible] hVal in
private theorem swap_f1_locals_eq (s : ProgramState) :
    (swap_f1 s).locals = ⟨s.locals.a, s.locals.b, hVal s.globals.rawHeap s.locals.a⟩ := by
  show (⟨s.globals, ⟨s.locals.a, s.locals.b, hVal s.globals.rawHeap s.locals.a⟩⟩ :
    ProgramState).locals = _; rfl

@[simp] private theorem swap_f1_locals_a (s : ProgramState) :
    (swap_f1 s).locals.a = s.locals.a := by rw [swap_f1_locals_eq]
@[simp] private theorem swap_f1_locals_b (s : ProgramState) :
    (swap_f1 s).locals.b = s.locals.b := by rw [swap_f1_locals_eq]
attribute [local irreducible] hVal in
@[simp] private theorem swap_f1_locals_t (s : ProgramState) :
    (swap_f1 s).locals.t = hVal s.globals.rawHeap s.locals.a := by rw [swap_f1_locals_eq]

-- swap_f2: ⟨⟨heapUpdate s.globals.rawHeap s.locals.a (hVal s.globals.rawHeap s.locals.b)⟩, s.locals⟩
attribute [local irreducible] hVal heapUpdate in
private theorem swap_f2_globals_eq (s : ProgramState) :
    (swap_f2 s).globals =
      ⟨heapUpdate s.globals.rawHeap s.locals.a (hVal s.globals.rawHeap s.locals.b)⟩ := by
  show (⟨⟨heapUpdate s.globals.rawHeap s.locals.a (hVal s.globals.rawHeap s.locals.b)⟩,
    s.locals⟩ : ProgramState).globals = _; rfl

attribute [local irreducible] hVal heapUpdate in
@[simp] private theorem swap_f2_globals_rawHeap (s : ProgramState) :
    (swap_f2 s).globals.rawHeap = heapUpdate s.globals.rawHeap s.locals.a
      (hVal s.globals.rawHeap s.locals.b) := by rw [swap_f2_globals_eq]

attribute [local irreducible] hVal heapUpdate in
@[simp] private theorem swap_f2_locals (s : ProgramState) :
    (swap_f2 s).locals = s.locals := by
  show (⟨⟨heapUpdate s.globals.rawHeap s.locals.a (hVal s.globals.rawHeap s.locals.b)⟩,
    s.locals⟩ : ProgramState).locals = _; rfl

@[simp] private theorem swap_f2_locals_a (s : ProgramState) :
    (swap_f2 s).locals.a = s.locals.a := by rw [swap_f2_locals]
@[simp] private theorem swap_f2_locals_b (s : ProgramState) :
    (swap_f2 s).locals.b = s.locals.b := by rw [swap_f2_locals]
@[simp] private theorem swap_f2_locals_t (s : ProgramState) :
    (swap_f2 s).locals.t = s.locals.t := by rw [swap_f2_locals]

-- swap_f3: ⟨⟨heapUpdate s.globals.rawHeap s.locals.b s.locals.t⟩, s.locals⟩
attribute [local irreducible] heapUpdate in
private theorem swap_f3_globals_eq (s : ProgramState) :
    (swap_f3 s).globals = ⟨heapUpdate s.globals.rawHeap s.locals.b s.locals.t⟩ := by
  show (⟨⟨heapUpdate s.globals.rawHeap s.locals.b s.locals.t⟩,
    s.locals⟩ : ProgramState).globals = _; rfl

attribute [local irreducible] heapUpdate in
@[simp] private theorem swap_f3_globals_rawHeap (s : ProgramState) :
    (swap_f3 s).globals.rawHeap = heapUpdate s.globals.rawHeap s.locals.b s.locals.t := by
  rw [swap_f3_globals_eq]

attribute [local irreducible] heapUpdate in
@[simp] private theorem swap_f3_locals (s : ProgramState) :
    (swap_f3 s).locals = s.locals := by
  show (⟨⟨heapUpdate s.globals.rawHeap s.locals.b s.locals.t⟩,
    s.locals⟩ : ProgramState).locals = _; rfl

@[simp] private theorem swap_f3_locals_a (s : ProgramState) :
    (swap_f3 s).locals.a = s.locals.a := by rw [swap_f3_locals]
@[simp] private theorem swap_f3_locals_b (s : ProgramState) :
    (swap_f3 s).locals.b = s.locals.b := by rw [swap_f3_locals]

-- heapPtrValid preservation lemmas
private theorem swap_f1_heapPtrValid_a (s : ProgramState)
    (h : heapPtrValid s.globals.rawHeap s.locals.a) :
    heapPtrValid (swap_f1 s).globals.rawHeap (swap_f1 s).locals.a := by
  simp only [swap_f1_globals, swap_f1_locals_a]; exact h

private theorem swap_f1_heapPtrValid_b (s : ProgramState)
    (h : heapPtrValid s.globals.rawHeap s.locals.b) :
    heapPtrValid (swap_f1 s).globals.rawHeap (swap_f1 s).locals.b := by
  simp only [swap_f1_globals, swap_f1_locals_b]; exact h

private theorem swap_f2_f1_heapPtrValid_b (s : ProgramState)
    (_h_va : heapPtrValid s.globals.rawHeap s.locals.a)
    (h_vb : heapPtrValid s.globals.rawHeap s.locals.b) :
    heapPtrValid (swap_f2 (swap_f1 s)).globals.rawHeap (swap_f2 (swap_f1 s)).locals.b := by
  simp only [swap_f2_globals_rawHeap, swap_f2_locals_b, swap_f1_globals, swap_f1_locals_a,
             swap_f1_locals_b]
  exact heapUpdate_preserves_heapPtrValid s.globals.rawHeap s.locals.a _ s.locals.b h_vb

private theorem swap_body_decomposed_results (s : ProgramState)
    (h_va : heapPtrValid s.globals.rawHeap s.locals.a)
    (h_vb : heapPtrValid s.globals.rawHeap s.locals.b) :
    ¬(swap_body_decomposed s).failed ∧
    ∀ (r : Except Unit Unit) (s' : ProgramState),
      (r, s') ∈ (swap_body_decomposed s).results →
      r = Except.ok () ∧
      s'.globals.rawHeap = heapUpdate
        (heapUpdate s.globals.rawHeap s.locals.a (hVal s.globals.rawHeap s.locals.b))
        s.locals.b (hVal s.globals.rawHeap s.locals.a) ∧
      s'.locals.a = s.locals.a ∧
      s'.locals.b = s.locals.b := by
  -- Step 1: guard(ptrValid a) >> modify(swap_f1)
  have h1 := L1_guard_modify_result
    (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.a) swap_f1 s h_va
  have h_step1_res : (swap_l1_step1 s).results = {(Except.ok (), swap_f1 s)} := by
    unfold swap_l1_step1; exact h1.1
  have h_step1_nf : ¬(swap_l1_step1 s).failed := by unfold swap_l1_step1; exact h1.2
  -- Step 2: guard(ptrValid a) >> guard(ptrValid b) >> modify(swap_f2)
  have h_va1 := swap_f1_heapPtrValid_a s h_va
  have h_vb1 := swap_f1_heapPtrValid_b s h_vb
  have h2 := L1_guard_guard_modify_result
    (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.a)
    (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.b)
    swap_f2 (swap_f1 s) h_va1 h_vb1
  have h_step2_res : (swap_l1_step2 (swap_f1 s)).results =
      {(Except.ok (), swap_f2 (swap_f1 s))} := by
    unfold swap_l1_step2; exact h2.1
  have h_step2_nf : ¬(swap_l1_step2 (swap_f1 s)).failed := by
    unfold swap_l1_step2; exact h2.2
  -- Step 3: guard(ptrValid b) >> modify(swap_f3)
  have h_vb2 := swap_f2_f1_heapPtrValid_b s h_va h_vb
  have h3 := L1_guard_modify_result
    (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.b)
    swap_f3 (swap_f2 (swap_f1 s)) h_vb2
  have h_step3_res : (swap_l1_step3 (swap_f2 (swap_f1 s))).results =
      {(Except.ok (), swap_f3 (swap_f2 (swap_f1 s)))} := by
    unfold swap_l1_step3; exact h3.1
  have h_step3_nf : ¬(swap_l1_step3 (swap_f2 (swap_f1 s))).failed := by
    unfold swap_l1_step3; exact h3.2
  -- Chain: seq step2 step3 at (swap_f1 s)
  have h_seq23 := L1_seq_singleton_ok h_step2_res h_step2_nf (m₂ := swap_l1_step3)
  have h_seq23_res : (L1.seq swap_l1_step2 swap_l1_step3 (swap_f1 s)).results =
      {(Except.ok (), swap_f3 (swap_f2 (swap_f1 s)))} := by
    rw [h_seq23.1, h_step3_res]
  have h_seq23_nf : ¬(L1.seq swap_l1_step2 swap_l1_step3 (swap_f1 s)).failed :=
    fun hf => h_step3_nf (h_seq23.2.mp hf)
  -- Chain: seq step1 (seq step2 step3) at s
  have h_inner := L1_seq_singleton_ok h_step1_res h_step1_nf
    (m₂ := L1.seq swap_l1_step2 swap_l1_step3)
  have h_inner_res : (L1.seq swap_l1_step1 (L1.seq swap_l1_step2 swap_l1_step3) s).results =
      {(Except.ok (), swap_f3 (swap_f2 (swap_f1 s)))} := by
    rw [h_inner.1, h_seq23_res]
  have h_inner_nf : ¬(L1.seq swap_l1_step1 (L1.seq swap_l1_step2 swap_l1_step3) s).failed :=
    fun hf => h_seq23_nf (h_inner.2.mp hf)
  -- Outer catch: catch inner skip
  have h_catch := L1_catch_singleton_ok h_inner_res h_inner_nf
  -- Now unfold swap_body_decomposed and conclude
  unfold swap_body_decomposed
  constructor
  · exact h_catch.2
  · intro r s' h_mem
    rw [h_catch.1] at h_mem
    have heq := Prod.mk.inj h_mem
    have hr := heq.1; have hs := heq.2
    subst hr; subst hs
    -- Final state projections via simp lemmas
    refine ⟨rfl, ?_, ?_, ?_⟩
    · -- s'.globals.rawHeap: chain swap_f3 -> swap_f2 -> swap_f1 projections
      simp only [swap_f3_globals_rawHeap, swap_f2_globals_rawHeap, swap_f2_locals_b,
                  swap_f2_locals_t, swap_f1_globals, swap_f1_locals_a, swap_f1_locals_b,
                  swap_f1_locals_t]
    · -- s'.locals.a
      simp only [swap_f3_locals_a, swap_f2_locals_a, swap_f1_locals_a]
    · -- s'.locals.b
      simp only [swap_f3_locals_b, swap_f2_locals_b, swap_f1_locals_b]

/-- Swap does not fail and produces the expected postcondition. -/
theorem l1_swap_validHoare (va vb : UInt32) :
    validHoare
      (fun s : ProgramState =>
        heapPtrValid s.globals.rawHeap s.locals.a ∧
        heapPtrValid s.globals.rawHeap s.locals.b ∧
        ptrDisjoint s.locals.a s.locals.b ∧
        hVal s.globals.rawHeap s.locals.a = va ∧
        hVal s.globals.rawHeap s.locals.b = vb)
      Swap.l1_swap_body
      (fun r s =>
        match r with
        | Except.ok () =>
          hVal s.globals.rawHeap s.locals.a = vb ∧
          hVal s.globals.rawHeap s.locals.b = va
        | Except.error () => True) := by
  rw [← swap_body_decomposed_eq]
  intro s ⟨h_va, h_vb, h_disj, h_val_a, h_val_b⟩
  have ⟨h_nf, h_post⟩ := swap_body_decomposed_results s h_va h_vb
  constructor
  · exact h_nf
  · intro r s' h_mem
    obtain ⟨h_r, h_heap, h_a, h_b⟩ := h_post r s' h_mem
    subst h_r
    have hba := heapPtrValid_bound h_va
    have hbb := heapPtrValid_bound h_vb
    constructor
    · rw [h_heap, h_a]
      rw [hVal_heapUpdate_disjoint _ _ _ _ hbb hba (ptrDisjoint_symm h_disj)]
      rw [hVal_heapUpdate_same _ _ _ hba]
      exact h_val_b
    · rw [h_heap, h_b]
      rw [hVal_heapUpdate_same _ _ _ hbb]
      exact h_val_a

/-! # The expected final state after swap. -/

noncomputable def swapFinalHeap (s : ProgramState) : HeapRawState :=
  heapUpdate
    (heapUpdate s.globals.rawHeap s.locals.a (hVal s.globals.rawHeap s.locals.b))
    s.locals.b
    (hVal s.globals.rawHeap s.locals.a)

/-- Swap exchanges the values at the two pointer locations. -/
theorem swap_values_exchanged (s : ProgramState)
    (h_va : heapPtrValid s.globals.rawHeap s.locals.a)
    (h_vb : heapPtrValid s.globals.rawHeap s.locals.b)
    (h_disj : ptrDisjoint s.locals.a s.locals.b) :
    hVal (swapFinalHeap s) s.locals.a = hVal s.globals.rawHeap s.locals.b ∧
    hVal (swapFinalHeap s) s.locals.b = hVal s.globals.rawHeap s.locals.a := by
  unfold swapFinalHeap
  have hba := heapPtrValid_bound h_va
  have hbb := heapPtrValid_bound h_vb
  exact ⟨by rw [hVal_heapUpdate_disjoint _ _ _ _ hbb hba (ptrDisjoint_symm h_disj),
                hVal_heapUpdate_same _ _ _ hba],
         hVal_heapUpdate_same _ _ _ hbb⟩

/-! # End-to-end: C-level correctness via L1corres bridge -/

theorem swap_correct (va vb : UInt32) :
    cHoare Swap.procEnv
      (fun s : ProgramState =>
        heapPtrValid s.globals.rawHeap s.locals.a ∧
        heapPtrValid s.globals.rawHeap s.locals.b ∧
        ptrDisjoint s.locals.a s.locals.b ∧
        hVal s.globals.rawHeap s.locals.a = va ∧
        hVal s.globals.rawHeap s.locals.b = vb)
      Swap.swap_body
      (fun s =>
        hVal s.globals.rawHeap s.locals.a = vb ∧
        hVal s.globals.rawHeap s.locals.b = va)
      (fun _ => True) :=
  L1corres_cHoare_bridge Swap.l1_swap_body_corres (l1_swap_validHoare va vb)

#print axioms Swap.l1_swap_body_corres
#print axioms swap_values_exchanged
#print axioms swap_correct
