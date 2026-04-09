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
set_option maxRecDepth 4096

open Swap

/-! # L1 monadic version of swap_body -/

noncomputable def l1_swap_body : L1Monad ProgramState :=
  L1.catch
    (L1.seq
      (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.a))
        (L1.modify (fun s =>
          { s with locals := { s.locals with t := hVal s.globals.rawHeap s.locals.a } })))
      (L1.seq
        (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.a))
          (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.b))
            (L1.modify (fun s =>
              { s with globals := { s.globals with
                rawHeap := heapUpdate s.globals.rawHeap s.locals.a
                  (hVal s.globals.rawHeap s.locals.b) } }))))
        (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.b))
          (L1.modify (fun s =>
            { s with globals := { s.globals with
              rawHeap := heapUpdate s.globals.rawHeap s.locals.b s.locals.t } })))))
    L1.skip

/-! # L1corres proof (sorry-free) -/

theorem l1_swap_body_corres :
    L1corres Swap.procEnv l1_swap_body Swap.swap_body := by
  unfold l1_swap_body Swap.swap_body
  apply L1corres_catch
  · apply L1corres_seq
    · apply L1corres_guard
      exact L1corres_basic _ _
    · apply L1corres_seq
      · apply L1corres_guard
        apply L1corres_guard
        exact L1corres_basic _ _
      · apply L1corres_guard
        exact L1corres_basic _ _
  · exact L1corres_skip _

/-! # validHoare: direct computation proof

    Known blocker (task-0062): Lean 4's {s with ...} desugars to
    `have __src := s.field` in some contexts and `let __src := s.field`
    in others. These are NOT definitionally equal for non-Prop types.
    This prevents composing L1 result lemmas with theorem statements.

    The l1_swap_validHoare proof is deferred to Phase 4 where a VCG
    tactic will normalize the have/let forms before applying rules.

    The sep-logic level proof (swap_sep_correct in SepLogic.lean and
    swap_heapLift_corres in SwapHeapLift.lean) is complete and sorry-free,
    demonstrating that the HeapLift layer works correctly. -/

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
  sorry

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
