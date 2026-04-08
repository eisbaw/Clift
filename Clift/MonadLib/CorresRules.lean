-- Correspondence rules: transitivity, guard weakening, sequential composition
--
-- These are the workhorse lemmas for the lifting pipeline.
-- corres_trans chains L1->L2->...->L5 into end-to-end refinement.
-- corres_guard_imp weakens preconditions.
-- corres_split handles sequential composition of corres proofs.
--
-- Reference: ext/AutoCorres2/CorresXF.thy (corresXF_guard_imp, corresXF_join)

import Clift.MonadLib.Corres

/-! # Guard weakening -/

/-- Guard weakening: if corres holds with stronger guards Q/Q',
    and P implies Q and P' implies Q', then corres holds with P/P'.

    This is the correspondence analogue of Hoare logic's consequence rule. -/
theorem corres_guard_imp
    {σ σ' α β : Type}
    {srel : σ → σ' → Prop}
    {nf nf' : Bool}
    {rrel : α → β → Prop}
    {P Q : σ → Prop} {P' Q' : σ' → Prop}
    {m : NondetM σ α} {m' : NondetM σ' β}
    (h : corres srel nf nf' rrel Q Q' m m')
    (h_guard : ∀ s, P s → Q s)
    (h_guard' : ∀ s', P' s' → Q' s') :
    corres srel nf nf' rrel P P' m m' := by
  intro s s' h_srel h_P h_P'
  exact h s s' h_srel (h_guard s h_P) (h_guard' s' h_P')

/-! # Transitivity -/

/-- Transitivity of corres: chains two refinement steps.

    The first step must have nf'=true (intermediate does not fail).
    This ensures the second step can find intermediate results.

    Guards on the intermediate state are True for composability.
    Use corres_guard_imp to adjust guards as needed. -/
theorem corres_trans
    {σ₁ σ₂ σ₃ : Type} {α₁ α₂ α₃ : Type}
    {srel₁ : σ₁ → σ₂ → Prop} {srel₂ : σ₂ → σ₃ → Prop}
    {rrel₁ : α₁ → α₂ → Prop} {rrel₂ : α₂ → α₃ → Prop}
    {nf₁ : Bool} {nf₂' : Bool}
    {G₁ : σ₁ → Prop} {G₃ : σ₃ → Prop}
    {m₁ : NondetM σ₁ α₁} {m₂ : NondetM σ₂ α₂} {m₃ : NondetM σ₃ α₃}
    (h₁ : corres srel₁ nf₁ true rrel₁ G₁ (fun _ => True) m₁ m₂)
    (h₂ : corres srel₂ true nf₂' rrel₂ (fun _ => True) G₃ m₂ m₃) :
    corres (fun s₁ s₃ => ∃ s₂, srel₁ s₁ s₂ ∧ srel₂ s₂ s₃)
      nf₁ nf₂'
      (fun r₁ r₃ => ∃ r₂, rrel₁ r₁ r₂ ∧ rrel₂ r₂ r₃)
      G₁ G₃ m₁ m₃ := by
  intro s₁ s₃ h_srel h_G₁ h_G₃
  obtain ⟨s₂, h_srel₁, h_srel₂⟩ := h_srel
  have h₁_facts := h₁ s₁ s₂ h_srel₁ h_G₁ trivial
  have h₂_facts := h₂ s₂ s₃ h_srel₂ trivial h_G₃
  obtain ⟨h₁_nf, h₁_match, h₁_nf'⟩ := h₁_facts
  obtain ⟨h₂_nf, h₂_match, h₂_nf'⟩ := h₂_facts
  refine ⟨?_, ?_, ?_⟩
  · exact h₁_nf
  · intro r₃ t₃ h_mem₃
    obtain ⟨r₂, t₂, h_mem₂, h_srel₂_t, h_rrel₂⟩ := h₂_match r₃ t₃ h_mem₃
    obtain ⟨r₁, t₁, h_mem₁, h_srel₁_t, h_rrel₁⟩ := h₁_match r₂ t₂ h_mem₂
    exact ⟨r₁, t₁, h_mem₁, ⟨t₂, h_srel₁_t, h_srel₂_t⟩, ⟨r₂, h_rrel₁, h_rrel₂⟩⟩
  · exact h₂_nf'

/-! # Sequential composition (split) -/

/-- Sequential composition of corres proofs (bind/split).

    If the first computations correspond, and the continuations correspond
    for every related pair of results and states, then the composed
    computations correspond.

    Subtlety: abstract no-fail for bind requires that ALL abstract
    continuations don't fail (not just those matching concrete results).
    This is handled by the h_abs_nf argument. -/
theorem corres_split
    {σ σ' α α' β β' : Type}
    {srel : σ → σ' → Prop}
    {nf nf' : Bool}
    {rrel₁ : α → α' → Prop}
    {rrel₂ : β → β' → Prop}
    {G : σ → Prop} {G' : σ' → Prop}
    {m₁ : NondetM σ α} {m₁' : NondetM σ' α'}
    {m₂ : α → NondetM σ β} {m₂' : α' → NondetM σ' β'}
    (h₁ : corres srel nf nf' rrel₁ G G' m₁ m₁')
    (h₂ : ∀ r r' t t', rrel₁ r r' → srel t t' →
        corres srel nf nf' rrel₂ (fun _ => True) (fun _ => True) (m₂ r) (m₂' r'))
    (h_abs_nf : nf = true → ∀ s, G s →
        ∀ a t, (a, t) ∈ (m₁ s).results → ¬(m₂ a t).failed)
    : corres srel nf nf' rrel₂ G G' (m₁ >>= m₂) (m₁' >>= m₂') := by
  intro s s' h_srel h_G h_G'
  obtain ⟨h₁_nf, h₁_match, h₁_nf'⟩ := h₁ s s' h_srel h_G h_G'
  refine ⟨?_, ?_, ?_⟩
  · -- abstract no-fail
    intro h_nf_eq h_fail
    simp at h_fail
    rcases h_fail with h_m₁_fail | ⟨a, t, h_mem₁, h_m₂_fail⟩
    · exact h₁_nf h_nf_eq h_m₁_fail
    · exact h_abs_nf h_nf_eq s h_G a t h_mem₁ h_m₂_fail
  · -- result matching
    intro r' t_final' h_mem
    simp at h_mem
    obtain ⟨a', t', h_mem₁', h_mem₂'⟩ := h_mem
    obtain ⟨a, t, h_mem₁, h_srel_t, h_rrel₁⟩ := h₁_match a' t' h_mem₁'
    have h₂_inst := h₂ a a' t t' h_rrel₁ h_srel_t
    obtain ⟨_, h₂_match, _⟩ := h₂_inst t t' h_srel_t trivial trivial
    obtain ⟨r, t_final, h_mem₂, h_srel_final, h_rrel₂⟩ := h₂_match r' t_final' h_mem₂'
    exact ⟨r, t_final, ⟨a, t, h_mem₁, h_mem₂⟩, h_srel_final, h_rrel₂⟩
  · -- concrete no-fail
    intro h_nf'_eq h_fail
    simp at h_fail
    rcases h_fail with h_m₁'_fail | ⟨a', t', h_mem₁', h_m₂'_fail⟩
    · exact h₁_nf' h_nf'_eq h_m₁'_fail
    · obtain ⟨a, t, h_mem₁, h_srel_t, h_rrel₁⟩ := h₁_match a' t' h_mem₁'
      have h₂_inst := h₂ a a' t t' h_rrel₁ h_srel_t
      obtain ⟨_, _, h₂_nf'⟩ := h₂_inst t t' h_srel_t trivial trivial
      exact h₂_nf' h_nf'_eq h_m₂'_fail

/-- corres_split when nf=false: no abstract no-fail obligation.
    This is the common case for partial correctness proofs. -/
theorem corres_split_nf_false
    {σ σ' α α' β β' : Type}
    {srel : σ → σ' → Prop}
    {nf' : Bool}
    {rrel₁ : α → α' → Prop}
    {rrel₂ : β → β' → Prop}
    {G : σ → Prop} {G' : σ' → Prop}
    {m₁ : NondetM σ α} {m₁' : NondetM σ' α'}
    {m₂ : α → NondetM σ β} {m₂' : α' → NondetM σ' β'}
    (h₁ : corres srel false nf' rrel₁ G G' m₁ m₁')
    (h₂ : ∀ r r' t t', rrel₁ r r' → srel t t' →
        corres srel false nf' rrel₂ (fun _ => True) (fun _ => True) (m₂ r) (m₂' r'))
    : corres srel false nf' rrel₂ G G' (m₁ >>= m₂) (m₁' >>= m₂') :=
  corres_split h₁ h₂ (fun h => Bool.noConfusion h)

/-- Corres for fail on both sides: trivially holds (no concrete results). -/
theorem corres_fail_fail
    {σ σ' α β : Type}
    {srel : σ → σ' → Prop}
    {rrel : α → β → Prop}
    {G : σ → Prop} {G' : σ' → Prop} :
    corres srel false false rrel G G'
      (NondetM.fail : NondetM σ α) (NondetM.fail : NondetM σ' β) := by
  intro s s' _ _ _
  refine ⟨fun h => Bool.noConfusion h, ?_, fun h => Bool.noConfusion h⟩
  intro r' t' h_mem
  simp at h_mem
