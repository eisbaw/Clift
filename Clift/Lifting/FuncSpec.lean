-- FuncSpec: Function specification framework for verified C functions
--
-- Each verified function gets a FuncSpec: a Hoare triple (precondition,
-- postcondition) that describes its behavior. Callers use the SPEC at call
-- sites, not the function body. This is how verification scales: verifying
-- a caller does not require inlining the entire callee.
--
-- Design: FuncSpec is simply a record wrapping a validHoare statement.
-- The key theorem is L1_hoare_call_spec: at a call site, if the callee
-- satisfies its spec, and the caller's precondition implies the callee's
-- precondition (after state setup), then the caller can use the callee's
-- postcondition.
--
-- Reference: seL4's ccorres_call, AutoCorres2's function_info.ML

import Clift.Lifting.L1HoareRules
import Clift.Lifting.SimplConv

/-! # Function specification -/

/-- A function specification: precondition and postcondition for an L1 function.
    The postcondition takes the Except return value and final state.

    A function satisfies its spec if `validHoare pre body post` holds. -/
structure FuncSpec (σ : Type) where
  /-- Precondition on the initial state -/
  pre  : σ → Prop
  /-- Postcondition on the return value and final state -/
  post : Except Unit Unit → σ → Prop

namespace FuncSpec

variable {σ : Type}

/-- A function body satisfies its specification. -/
def satisfiedBy (spec : FuncSpec σ) (body : L1Monad σ) : Prop :=
  validHoare spec.pre body spec.post

/-- At a call site, use the callee's spec to derive the caller's postcondition.

    Given:
    - The callee's body satisfies its spec
    - The caller's precondition P implies the callee's precondition
    - The callee's postcondition implies the caller's intermediate condition R

    Then validHoare P calleeBody R. -/
theorem call_spec (spec : FuncSpec σ) (body : L1Monad σ)
    (P : σ → Prop) (R : Except Unit Unit → σ → Prop)
    (h_sat : spec.satisfiedBy body)
    (h_pre : ∀ s, P s → spec.pre s)
    (h_post : ∀ r s, spec.post r s → R r s) :
    validHoare P body R := by
  intro s₀ hp
  have ⟨h_nf, h_post_body⟩ := h_sat s₀ (h_pre s₀ hp)
  exact ⟨h_nf, fun r s₁ h_mem => h_post r s₁ (h_post_body r s₁ h_mem)⟩

/-- Specialized call_spec for the common case where pre/post are used directly. -/
theorem call_spec_exact (spec : FuncSpec σ) (body : L1Monad σ)
    (h_sat : spec.satisfiedBy body) :
    validHoare spec.pre body spec.post :=
  h_sat

end FuncSpec

/-! # L1 Hoare rule for call via spec

When we have:
- L1corres Γ l1Body csimplBody (the L1 body corresponds to CSimpl)
- validHoare P l1Body Q (the L1 body satisfies a spec)
- The call resolves to this body in the procedure environment

Then at the L1 level, we can use the spec for the call. -/

/-- Hoare rule for L1.call using a function spec.

    If the L1ProcEnv maps `name` to `l1Body`, and `l1Body` satisfies spec,
    and the caller's precondition implies the spec's precondition,
    then validHoare holds for the call. -/
theorem L1_hoare_call_spec {σ : Type}
    (l1Γ : L1.L1ProcEnv σ) (name : ProcName) (l1Body : L1Monad σ)
    (P : σ → Prop) (Q : Except Unit Unit → σ → Prop)
    (h_lookup : l1Γ name = some l1Body)
    (h_body : validHoare P l1Body Q) :
    validHoare P (L1.call l1Γ name) Q := by
  intro s₀ hp
  -- L1.call l1Γ name unfolds to l1Body since l1Γ name = some l1Body
  have h_eq : L1.call l1Γ name = l1Body := by
    simp [L1.call, h_lookup]
  rw [h_eq]
  exact h_body s₀ hp

/-- Hoare rule for L1.dynCom: if for the current state s, the command (f s)
    satisfies Hoare triple P → Q, then dynCom f satisfies P → Q.

    The precondition must be strong enough that P s implies validHoare holds
    for f s. -/
theorem L1_hoare_dynCom {σ : Type}
    (f : σ → L1Monad σ)
    (P : σ → Prop) (Q : Except Unit Unit → σ → Prop)
    (h : ∀ s, P s → validHoare (fun s' => s' = s ∧ P s') (f s) Q) :
    validHoare P (L1.dynCom f) Q := by
  intro s₀ hp
  have h_spec := h s₀ hp
  -- L1.dynCom f at s₀ evaluates f s₀ at s₀
  -- So (L1.dynCom f s₀) = (f s₀ s₀)
  have ⟨h_nf, h_post⟩ := h_spec s₀ ⟨rfl, hp⟩
  exact ⟨h_nf, h_post⟩

/-! # Composition: caller verifies using callee specs

The workflow for multi-function verification:
1. For each function f, prove `FuncSpec.satisfiedBy spec_f l1_f_body`
2. In the caller's proof, use `L1_hoare_call_spec` at call sites
   to apply the callee's spec instead of inlining the body
3. The VCG tactic (task 0087) will do this automatically
-/
