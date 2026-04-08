-- Correspondence (refinement) relation: backward simulation following seL4
--
-- This is the most critical definition in the entire pipeline.
-- If corres is wrong, every downstream proof is unsound.
--
-- Design: plan.md Decision 1 (backward simulation)
-- Reference: ext/AutoCorres2/CorresXF.thy (corresXF_simple, corresXF)
--
-- Backward simulation means: for every concrete result, there exists
-- a matching abstract result. The abstract is an overapproximation
-- of the concrete. Properties proved about the abstract hold for
-- the concrete because the concrete cannot do anything the abstract cannot.

import Clift.MonadLib.NondetM

/-! # Correspondence relation (backward simulation) -/

/-- Backward simulation refinement relation.

    `corres srel nf nf' rrel G G' m m'` states that
    the concrete computation `m'` (in state type `σ'`) is refined by
    the abstract computation `m` (in state type `σ`).

    Parameters:
    - `srel`: relates abstract states to concrete states
    - `nf`:   no-fail flag for abstract side (when true, abstract must not fail)
    - `nf'`:  no-fail flag for concrete side (when true, concrete must not fail)
    - `rrel`: relates abstract return values to concrete return values
    - `G`:    guard (precondition) on abstract state
    - `G'`:   guard (precondition) on concrete state
    - `m`:    abstract computation
    - `m'`:   concrete computation

    The relation says: given related states satisfying guards,
    1. For every concrete result `(r', t')`, there exists a matching
       abstract result `(r, t)` with related states and return values.
    2. If `nf` is true, the abstract must not fail.
    3. If `nf'` is true, the concrete must not fail.

    This is a BACKWARD simulation: we look at what the concrete does
    and require the abstract to match. The abstract may have additional
    behaviors (nondeterminism) that the concrete does not exercise.

    Gotcha: the no-fail conditions are checked AFTER establishing
    the state relation and guards, but BEFORE examining results.
    This matches seL4's corres_underlying where succeeds(abstract)
    is a precondition for the result matching. -/
def corres
    {σ σ' : Type} {α β : Type}
    (srel : σ → σ' → Prop)
    (nf : Bool) (nf' : Bool)
    (rrel : α → β → Prop)
    (G : σ → Prop) (G' : σ' → Prop)
    (m : NondetM σ α)
    (m' : NondetM σ' β)
    : Prop :=
  ∀ s s', srel s s' → G s → G' s' →
    -- no-fail abstract: if nf, abstract must not fail
    (nf = true → ¬(m s).failed) ∧
    -- result matching: every concrete result has a matching abstract result
    (∀ r' t', (r', t') ∈ (m' s').results →
      ∃ r t, (r, t) ∈ (m s).results ∧ srel t t' ∧ rrel r r') ∧
    -- no-fail concrete: if nf', concrete must not fail
    (nf' = true → ¬(m' s').failed)

/-! # Basic corres lemmas -/

namespace corres

variable {σ σ' α β : Type}

/-- Sanity: corres holds trivially for pure computations with matching values. -/
theorem pure_pure (srel : σ → σ' → Prop) (rrel : α → β → Prop)
    (x : α) (y : β) (h : rrel x y) :
    corres srel true true rrel (fun _ => True) (fun _ => True)
      (Pure.pure x : NondetM σ α) (Pure.pure y : NondetM σ' β) := by
  intro s s' h_srel _ _
  refine ⟨?_, ?_, ?_⟩
  · -- abstract no-fail
    intro _
    simp
  · -- result matching
    intro r' t' h_mem
    simp at h_mem
    obtain ⟨rfl, rfl⟩ := h_mem
    exact ⟨x, s, rfl, h_srel, h⟩
  · -- concrete no-fail
    intro _
    simp

/-- Corres for identical pure computations (rrel = Eq, same state type, srel = Eq). -/
theorem pure_pure_eq (x : α) :
    corres (fun s s' => s = s') true true (fun a b => a = b)
      (fun _ => True) (fun _ => True)
      (Pure.pure x : NondetM σ α) (Pure.pure x : NondetM σ α) := by
  exact pure_pure (fun s s' => s = s') (fun a b => a = b) x x rfl

/-- Weakening: if corres holds with nf=true, it holds with nf=false. -/
theorem weaken_nf {srel : σ → σ' → Prop} {rrel : α → β → Prop}
    {G : σ → Prop} {G' : σ' → Prop}
    {m : NondetM σ α} {m' : NondetM σ' β}
    {nf' : Bool}
    (h : corres srel true nf' rrel G G' m m') :
    corres srel false nf' rrel G G' m m' := by
  intro s s' h_srel h_G h_G'
  obtain ⟨_, h_match, h_nf'⟩ := h s s' h_srel h_G h_G'
  exact ⟨fun h => Bool.noConfusion h, h_match, h_nf'⟩

/-- Weakening: if corres holds with nf'=true, it holds with nf'=false. -/
theorem weaken_nf' {srel : σ → σ' → Prop} {rrel : α → β → Prop}
    {G : σ → Prop} {G' : σ' → Prop}
    {m : NondetM σ α} {m' : NondetM σ' β}
    {nf : Bool}
    (h : corres srel nf true rrel G G' m m') :
    corres srel nf false rrel G G' m m' := by
  intro s s' h_srel h_G h_G'
  obtain ⟨h_nf, h_match, _⟩ := h s s' h_srel h_G h_G'
  exact ⟨h_nf, h_match, fun h => Bool.noConfusion h⟩

end corres
