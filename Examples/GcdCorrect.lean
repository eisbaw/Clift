-- Phase 1 end-to-end: gcd correctness proof chaining back to C semantics
--
-- Pipeline: C source -> CImporter -> CSimpl -> cHoare on Exec
--           AND: CSimpl -> L1 (SimplConv) -> L1corres (axiom-free)
--
-- This demonstrates the Phase 1 exit criterion: prove a property about
-- C code that chains all the way back to the Exec semantics.
-- We also show the L1corres bridge connecting L1 proofs to C semantics.

import Generated.Gcd
import Clift.Lifting.SimplConv
import Examples.GcdProof

set_option maxHeartbeats 3200000

open Gcd

/-! # Bridge lemma: L1corres + validHoare -> cHoare

This is the key theorem connecting the L1 monadic world to the CSimpl
Exec world. It says: if the L1 monad overapproximates the CSimpl Exec
semantics (L1corres), and the L1 monad satisfies a Hoare triple, then
the CSimpl program satisfies a corresponding Hoare triple.

The encoding maps:
- Normal Exec outcome -> Except.ok () in the L1 result
- Abrupt Exec outcome -> Except.error () in the L1 result
- Fault -> impossible (L1corres guarantees no fault when L1 doesn't fail)
-/

theorem L1corres_cHoare_bridge {σ : Type} {Γ : ProcEnv σ}
    {m : L1Monad σ} {c : CSimpl σ}
    (h_corres : L1corres Γ m c)
    {P : σ → Prop}
    {Q_ok : σ → Prop}    -- postcondition for normal outcomes
    {Q_err : σ → Prop}   -- postcondition for abrupt outcomes
    (h_hoare : validHoare P m (fun r s =>
      match r with
      | Except.ok () => Q_ok s
      | Except.error () => Q_err s)) :
    cHoare Γ P c Q_ok Q_err := by
  intro s h_P o h_exec
  have ⟨h_nf, h_post⟩ := h_hoare s h_P
  obtain ⟨h_ok, h_err, h_no_fault⟩ := h_corres s h_nf
  match o with
  | .normal s' =>
    have h_mem := h_ok s' h_exec
    exact h_post (Except.ok ()) s' h_mem
  | .abrupt s' =>
    have h_mem := h_err s' h_exec
    exact h_post (Except.error ()) s' h_mem
  | .fault =>
    exact absurd h_exec h_no_fault

/-! # Gcd base case: CSimpl-level proof using cHoare rules

When b = 0, the gcd body:
  catch (seq (while (b!=0) body) (seq (basic ret:=a) throw)) skip
reduces to:
  catch (seq skip (seq (basic ret:=a) throw)) skip
  = catch (seq (basic ret:=a) throw) skip
  = normal outcome with ret_val = a

We prove this directly using the CSimpl Hoare rules from HoareDef.lean.
-/

/-- While loop with false initial condition: partial correctness with any invariant. -/
theorem cHoare_while_false {σ : Type} (Γ : ProcEnv σ) {b : σ → Bool}
    {c : CSimpl σ} {P : σ → Prop}
    (h_false : ∀ s, P s → b s = false) :
    cHoare Γ P (.while b c) P (fun _ => True) := by
  intro s hP o hExec
  -- When condition is false, only whileFalse fires
  cases hExec with
  | whileFalse _ _ _ hb => exact hP
  | whileTrue _ _ _ _ _ hb => exact absurd hb (by simp [h_false s hP])
  | whileAbrupt _ _ _ _ hb => exact absurd hb (by simp [h_false s hP])
  | whileFault _ _ _ hb => exact absurd hb (by simp [h_false s hP])

/-- Gcd base case: when b = 0, gcd_body terminates normally with ret_val = a.
    Proved directly on the CSimpl Exec semantics via case analysis on Exec. -/
theorem gcd_base_case :
    cHoare Gcd.procEnv
      (fun s : ProgramState => s.locals.b = 0)
      Gcd.gcd_body
      (fun s => s.locals.ret__val = s.locals.a)
      (fun _ => True) := by
  -- Direct proof: case-analyze the Exec derivation
  intro s h_b0 o h_exec
  unfold Gcd.gcd_body at h_exec
  -- h_exec : Exec Γ (catch (seq while (seq basic throw)) skip) s o
  cases h_exec with
  | catchNormal _ _ _ _ h_body =>
    -- Body completed normally: impossible because seq ends with throw
    cases h_body with
    | seqNormal _ _ _ t _ h_while h_rest =>
      cases h_while with
      | whileFalse _ _ _ hb =>
        cases h_rest with
        | seqNormal _ _ _ t2 _ h_basic h_throw =>
          cases h_basic with
          | basic _ _ => cases h_throw  -- throw never produces normal
      | whileTrue _ _ _ _ _ hb => simp [h_b0] at hb
  | catchAbrupt _ _ _ t _ h_body h_handler =>
    -- Body gave abrupt: while(false) -> basic(ret:=a) -> throw -> catch -> skip
    cases h_body with
    | seqNormal _ _ _ t' _ h_while h_rest =>
      cases h_while with
      | whileFalse _ _ _ hb =>
        cases h_rest with
        | seqNormal _ _ _ t2 _ h_basic h_throw =>
          cases h_basic with
          | basic _ _ =>
            cases h_throw with
            | throw =>
              cases h_handler with
              | skip => rfl
        | seqAbrupt _ _ _ _ h_basic =>
          cases h_basic  -- basic never gives abrupt
      | whileTrue _ _ _ _ _ hb => simp [h_b0] at hb
    | seqAbrupt _ _ _ _ h_while =>
      cases h_while with
      | whileTrue _ _ _ _ _ hb => simp [h_b0] at hb
      | whileAbrupt _ _ _ _ hb => simp [h_b0] at hb
  | catchFault _ _ _ h_body =>
    -- Body faulted: impossible when b=0 (loop never enters, guard unreachable)
    cases h_body with
    | seqFault _ _ _ h_while =>
      cases h_while with
      | whileTrue _ _ _ _ _ hb => simp [h_b0] at hb
      | whileFault _ _ _ hb => simp [h_b0] at hb
    | seqNormal _ _ _ t _ h_while h_rest =>
      cases h_while with
      | whileFalse _ _ _ hb =>
        cases h_rest with
        | seqNormal _ _ _ t2 _ h_basic h_throw =>
          cases h_basic with
          | basic _ _ => cases h_throw
        | seqFault _ _ _ h_basic => cases h_basic
      | whileTrue _ _ _ _ _ hb => simp [h_b0] at hb

/-! # Phase 1 end-to-end validation

We have demonstrated:
1. gcd.c -> CImporter -> Generated/Gcd.lean (CSimpl terms) -- compiles
2. CSimpl -> L1 monadic form (Examples/GcdProof.lean) -- l1_gcd_body
3. L1corres proof (l1_gcd_body_corres) -- all axioms now proved as theorems
4. Bridge lemma (L1corres_cHoare_bridge) -- connects L1 to CSimpl
5. Direct CSimpl-level proof (gcd_base_case) -- gcd(a,0) = a

The proof chain from gcd_base_case to the actual C code:
- gcd_base_case is stated in terms of Exec Γ gcd_body s outcome
- Exec is the big-step semantics for CSimpl
- gcd_body is the CSimpl term generated by CImporter from gcd.c
- Therefore, the theorem applies to the C program

The L1corres chain provides an ALTERNATIVE proof path:
- Prove properties at the L1 (NondetM) level using validHoare
- Use L1corres_cHoare_bridge to transfer to CSimpl
- This path will be the primary one once L1 Hoare rules are developed

Both paths terminate at Exec, which is the trusted semantic model.
-/

-- Sanity: verify the proof is axiom-free by checking #print axioms
#print axioms gcd_base_case
#print axioms L1corres_cHoare_bridge
#print axioms l1_gcd_body_corres
