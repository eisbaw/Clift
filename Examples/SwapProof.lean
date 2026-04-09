-- Phase 3a: swap correctness proof — first pointer verification test
--
-- Proves: after swap(&a, &b), *a and *b are exchanged.
-- Pipeline: swap.c -> CImporter -> CSimpl (Generated/Swap.lean)
--           -> L1 lifting -> L1corres_cHoare_bridge

import Generated.Swap
import Clift.Lifting.SimplConv
import Clift.Lifting.L1HoareRules
import Clift.MonadLib.HoareRules
import Examples.GcdCorrect  -- for L1corres_cHoare_bridge

set_option maxHeartbeats 12800000
set_option maxRecDepth 16384

open Swap

/-! # L1 monadic version of swap_body

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

noncomputable def l1_swap_body : L1Monad ProgramState :=
  L1.catch (L1.seq swap_l1_step1 (L1.seq swap_l1_step2 swap_l1_step3)) L1.skip

/-! # L1corres proof (sorry-free) -/

theorem l1_swap_body_corres :
    L1corres Swap.procEnv l1_swap_body Swap.swap_body := by
  unfold l1_swap_body swap_l1_step1 swap_l1_step2 swap_l1_step3 Swap.swap_body
  apply L1corres_catch
  · apply L1corres_seq
    · apply L1corres_guard; exact L1corres_basic _ _
    · apply L1corres_seq
      · apply L1corres_guard; apply L1corres_guard; exact L1corres_basic _ _
      · apply L1corres_guard; exact L1corres_basic _ _
  · exact L1corres_skip _

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

    The key insight: l1_swap_body is defined using L1 combinators (guard, modify,
    seq, catch). We unfold it directly and work with the L1 combinator definitions,
    avoiding any intermediate abbrevs that would create kernel checking depth. -/

/-- Helper: the result set and failure flag of l1_swap_body at state s.
    Proved by unfolding one combinator at a time, each at bounded depth.
    The outer catch/seq structure is handled via L1_catch_singleton_ok
    and L1_seq_singleton_ok, which produce FLAT proofs. -/
private theorem l1_swap_body_results (s : ProgramState)
    (h_va : heapPtrValid s.globals.rawHeap s.locals.a)
    (h_vb : heapPtrValid s.globals.rawHeap s.locals.b) :
    ¬(l1_swap_body s).failed ∧
    ∀ (r : Except Unit Unit) (s' : ProgramState),
      (r, s') ∈ (l1_swap_body s).results →
      r = Except.ok () ∧
      s'.globals.rawHeap = heapUpdate
        (heapUpdate s.globals.rawHeap s.locals.a (hVal s.globals.rawHeap s.locals.b))
        s.locals.b (hVal s.globals.rawHeap s.locals.a) ∧
      s'.locals.a = s.locals.a ∧
      s'.locals.b = s.locals.b := by
  -- l1_swap_body = catch (seq step1 (seq step2 step3)) skip
  -- Unfold the outermost layer only: l1_swap_body -> L1.catch inner skip
  unfold l1_swap_body
  have h1 := L1_guard_modify_result
    (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.a) swap_f1 s h_va
  have h_step1_res : (swap_l1_step1 s).results = {(Except.ok (), swap_f1 s)} := by
    unfold swap_l1_step1; exact h1.1
  have h_step1_nf : ¬(swap_l1_step1 s).failed := by unfold swap_l1_step1; exact h1.2
  -- BLOCKED: Lean 4 kernel deep recursion (task-0076).
  -- Even trivial type-checking of proof terms that involve structure projections
  -- through composed state transformation functions (swap_f1, swap_f2, swap_f3)
  -- hits the kernel's hardcoded recursion limit. For example, merely stating
  --   `have : heapPtrValid (swap_f1 s).globals.rawHeap ... := h_va`
  -- triggers deep recursion because the kernel must reduce (swap_f1 s).globals
  -- through the CState constructor.
  --
  -- The L1corres proof (l1_swap_body_corres) succeeds because it only needs
  -- to match L1 combinators structurally, not reduce through state projections.
  --
  -- Workaround: The HeapLift-level proof (SwapHeapLift.lean) is complete and
  -- sorry-free, demonstrating the pipeline works at the abstracted level.
  -- A MetaM-level VCG that builds flat proof terms without structure projections
  -- is needed to fix this (task-0071).
  sorry

/-- l1_swap_body does not fail and produces the expected postcondition. -/
theorem l1_swap_validHoare (va vb : UInt32) :
    validHoare
      (fun s : ProgramState =>
        heapPtrValid s.globals.rawHeap s.locals.a ∧
        heapPtrValid s.globals.rawHeap s.locals.b ∧
        ptrDisjoint s.locals.a s.locals.b ∧
        hVal s.globals.rawHeap s.locals.a = va ∧
        hVal s.globals.rawHeap s.locals.b = vb)
      l1_swap_body
      (fun r s =>
        match r with
        | Except.ok () =>
          hVal s.globals.rawHeap s.locals.a = vb ∧
          hVal s.globals.rawHeap s.locals.b = va
        | Except.error () => True) := by
  intro s ⟨h_va, h_vb, h_disj, h_val_a, h_val_b⟩
  have ⟨h_nf, h_post⟩ := l1_swap_body_results s h_va h_vb
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
  L1corres_cHoare_bridge l1_swap_body_corres (l1_swap_validHoare va vb)

#print axioms l1_swap_body_corres
#print axioms swap_values_exchanged
#print axioms swap_correct
