-- L2: Lift locals from state record into lambda-bound Lean variables + corres proof
--
-- Reference: ext/AutoCorres2/LocalVarExtract.thy, ext/AutoCorres2/L2Defs.thy
--
-- After L2, local variables are lambda-bound parameters, not fields of the
-- state record. The state contains only globals.
--
-- L2corres relates an L2 computation (over Globals, with locals as explicit
-- parameters) to an L1 computation (over CState Locals, with locals in state).
--
-- The abstraction: project CState to Globals via .globals, inject locals via
-- a reconstruction function. L2corres is parameterized by:
--   - proj: full state -> reduced state (always .globals)
--   - lift: reduced state -> full state (with fixed locals)
--
-- For Phase 1, L2 extraction is manual per-function.
-- MetaM automation to generate L2 definitions and proofs is future work (Phase 2+).

import Clift.Lifting.SimplConv

set_option maxHeartbeats 1600000

/-! # L2corres: correspondence between L1 (with locals in state) and L2 (locals extracted)

The key idea: an L2 computation operates on a *reduced* state (Globals only).
Local variables that were fields of the state become explicit parameters.

L2corres says: if we project the full state to the reduced state, run the L2
computation, then the result corresponds to running the L1 computation on the
full state.

Parameters:
- `proj`: project full state to reduced state (e.g., CState.globals)
- `lift`: reconstruct full state from reduced state (with fixed locals)
- `m2`: the L2 computation (over reduced state)
- `m1`: the L1 computation (over full state)
-/

/-- L2corres: an L2 computation (over reduced state σ₂) refines an L1
    computation (over full state σ₁) under a state projection.

    Specifically: for every full state s₁, if we project to σ₂ and run m2,
    then failure and results agree up to the projection/lifting.

    This is simpler than the general corres because L1 and L2 share the
    same return type — we're only changing the state type. -/
def L2corres {σ₁ σ₂ : Type} {α : Type}
    (proj : σ₁ → σ₂)
    (lift : σ₂ → σ₁)
    (m2 : NondetM σ₂ α)
    (m1 : NondetM σ₁ α) : Prop :=
  ∀ s₁,
    -- Roundtrip: lift ∘ proj = id on s₁ (for this particular state)
    lift (proj s₁) = s₁ →
    -- Failure agreement: m2 fails iff m1 fails
    ((m2 (proj s₁)).failed ↔ (m1 s₁).failed) ∧
    -- Forward: every m1 result maps to an m2 result
    (∀ r t₁, (r, t₁) ∈ (m1 s₁).results →
      (r, proj t₁) ∈ (m2 (proj s₁)).results) ∧
    -- Backward: every m2 result lifts to an m1 result
    (∀ r t₂, (r, t₂) ∈ (m2 (proj s₁)).results →
      (r, lift t₂) ∈ (m1 s₁).results)

/-! # L2corres composition lemmas -/

/-- L2corres preserves validHoare: if m2 satisfies a Hoare triple over reduced
    state, and L2corres holds, then m1 satisfies a corresponding Hoare triple
    over the full state (with projected pre/postconditions).

    The roundtrip hypothesis `lift (proj s₁) = s₁` must hold for states
    satisfying the precondition. This is natural when proj = .globals and
    lift reconstructs the CState with the same locals. -/
theorem L2corres_validHoare {σ₁ σ₂ α : Type}
    {proj : σ₁ → σ₂} {lift : σ₂ → σ₁}
    {m2 : NondetM σ₂ α} {m1 : NondetM σ₁ α}
    (hcorres : L2corres proj lift m2 m1)
    {P : σ₂ → Prop} {Q : α → σ₂ → Prop}
    (h2 : validHoare P m2 Q)
    (h_rt : ∀ s₁, P (proj s₁) → lift (proj s₁) = s₁) :
    validHoare (fun s₁ => P (proj s₁)) m1 (fun r s₁ => Q r (proj s₁)) := by
  intro s₁ hP
  have hrt := h_rt s₁ hP
  obtain ⟨h_fail, h_fwd, _⟩ := hcorres s₁ hrt
  obtain ⟨h_nf2, h_post2⟩ := h2 (proj s₁) hP
  constructor
  · intro hf; exact h_nf2 (h_fail.mpr hf)
  · intro r t₁ h_mem
    exact h_post2 r (proj t₁) (h_fwd r t₁ h_mem)

/-! # L2corres combinator lemmas

These enable compositional L2corres proofs: if L2corres holds for sub-computations,
it holds for their composition. This parallels the L1corres combinator lemmas. -/

/-- L2corres for L1.skip: the L2 version is also skip (identity on reduced state). -/
theorem L2corres_skip {σ₁ σ₂ : Type}
    {proj : σ₁ → σ₂} {lift : σ₂ → σ₁} :
    L2corres proj lift (L1.skip : L1Monad σ₂) (L1.skip : L1Monad σ₁) := by
  intro s₁ hrt
  unfold L1.skip NondetM.pure
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨fun h => h, fun h => h⟩
  · intro r t₁ h
    have h := Set.mem_singleton_iff.mp h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp at h1 h2; subst h1; subst h2; rfl
  · intro r t₂ h
    have h := Set.mem_singleton_iff.mp h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp at h1 h2; subst h1; subst h2
    simp only [Set.mem_singleton_iff]; exact congrArg _ hrt

/-- L2corres for L1.throw -/
theorem L2corres_throw {σ₁ σ₂ : Type}
    {proj : σ₁ → σ₂} {lift : σ₂ → σ₁} :
    L2corres proj lift (L1.throw : L1Monad σ₂) (L1.throw : L1Monad σ₁) := by
  intro s₁ hrt
  unfold L1.throw NondetM.pure
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨fun h => h, fun h => h⟩
  · intro r t₁ h
    have h := Set.mem_singleton_iff.mp h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp at h1 h2; subst h1; subst h2; rfl
  · intro r t₂ h
    have h := Set.mem_singleton_iff.mp h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp at h1 h2; subst h1; subst h2
    simp only [Set.mem_singleton_iff]; exact congrArg _ hrt

/-- L2corres for L1.modify: the modification function must commute with proj/lift. -/
theorem L2corres_modify {σ₁ σ₂ : Type}
    {proj : σ₁ → σ₂} {lift : σ₂ → σ₁}
    {f₂ : σ₂ → σ₂} {f₁ : σ₁ → σ₁}
    (h_comm : ∀ s₁, lift (proj s₁) = s₁ → proj (f₁ s₁) = f₂ (proj s₁))
    (h_lift : ∀ s₁, lift (proj s₁) = s₁ → lift (f₂ (proj s₁)) = f₁ s₁) :
    L2corres proj lift (L1.modify f₂) (L1.modify f₁) := by
  intro s₁ hrt
  unfold L1.modify
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨fun h => h, fun h => h⟩
  · intro r t₁ h
    have h := Set.mem_singleton_iff.mp h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp at h1 h2; subst h1; subst h2
    exact Set.mem_singleton_iff.mpr (congrArg _ (h_comm s₁ hrt))
  · intro r t₂ h
    have h := Set.mem_singleton_iff.mp h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp at h1 h2; subst h1; subst h2
    exact Set.mem_singleton_iff.mpr (congrArg _ (h_lift s₁ hrt))

/-! # Summary

L2corres is the formal bridge between L1 (locals in state) and L2 (locals extracted).
The definition requires:
1. Failure agreement between L2 and L1 computations
2. Forward simulation: L1 results project to L2 results
3. Backward simulation: L2 results lift to L1 results
4. A roundtrip condition: lift ∘ proj = id on relevant states

Key theorems:
- L2corres_validHoare: transfer Hoare triples from L2 level to L1 level
- L2corres_skip, L2corres_throw, L2corres_modify: compositional building blocks

Per-function L2corres proofs are demonstrated in Examples/GcdL2.lean (gcd)
and Examples/SwapL2.lean (swap). These are manual for now; MetaM automation
is future work (task-0071).
-/
