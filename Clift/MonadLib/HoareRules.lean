-- Hoare logic rules: skip, basic, seq, cond, while-invariant, frame
--
-- These are the building blocks for all verification in Clift.
-- Each rule is proven for both validHoare (partial) and totalHoare (total correctness).
--
-- Reference: ext/AutoCorres2/L1Defs.thy, Simpl's HoarePartialDef.thy

import Clift.MonadLib.Hoare

/-! # Sequential Hoare rules -/

section SkipBasicSeq

variable {σ α : Type}

/-- Skip rule: if P holds, skip preserves P. -/
theorem hoare_skip (P : Unit → σ → Prop) :
    validHoare (P ()) NondetM.skip P := by
  intro s₀ h_pre
  constructor
  · intro h_fail; exact h_fail
  · intro r s₁ h_mem
    have ⟨rfl, rfl⟩ := Prod.mk.inj h_mem
    exact h_pre

/-- Basic rule: to prove Q after applying f, prove Q ∘ f beforehand. -/
theorem hoare_basic (f : σ → σ) (Q : Unit → σ → Prop) :
    validHoare (fun s => Q () (f s)) (NondetM.basic f) Q := by
  intro s₀ h_pre
  constructor
  · intro h_fail; exact h_fail
  · intro r s₁ h_mem
    have h_eq : (r, s₁) = ((), f s₀) := h_mem
    rw [Prod.mk.injEq] at h_eq
    obtain ⟨rfl, rfl⟩ := h_eq
    exact h_pre

/-- Seq rule: if m₁ takes P to R, and m₂ takes R to Q, then seq takes P to Q. -/
theorem hoare_seq {P : σ → Prop} {R : Unit → σ → Prop} {Q : α → σ → Prop}
    {m₁ : NondetM σ Unit} {m₂ : NondetM σ α}
    (h₁ : validHoare P m₁ R)
    (h₂ : ∀ u, validHoare (R u) m₂ Q) :
    validHoare P (NondetM.seq m₁ m₂) Q := by
  intro s₀ h_pre
  have ⟨h_nf₁, h_post₁⟩ := h₁ s₀ h_pre
  constructor
  · -- no failure
    intro h_fail
    simp [NondetM.seq, NondetM.bind] at h_fail
    rcases h_fail with h_fail₁ | ⟨u, s', h_mem₁, h_fail₂⟩
    · exact h_nf₁ h_fail₁
    · have h_R := h_post₁ u s' h_mem₁
      exact (h₂ u s' h_R).1 h_fail₂
  · -- postcondition
    intro r s₁ h_mem
    simp [NondetM.seq, NondetM.bind] at h_mem
    obtain ⟨u, s', h_mem₁, h_mem₂⟩ := h_mem
    have h_R := h_post₁ u s' h_mem₁
    exact (h₂ u s' h_R).2 r s₁ h_mem₂

/-- Simplified seq rule where R doesn't depend on the unit value. -/
theorem hoare_seq' {P : σ → Prop} {R : σ → Prop} {Q : α → σ → Prop}
    {m₁ : NondetM σ Unit} {m₂ : NondetM σ α}
    (h₁ : validHoare P m₁ (fun _ s => R s))
    (h₂ : validHoare R m₂ Q) :
    validHoare P (NondetM.seq m₁ m₂) Q :=
  hoare_seq h₁ (fun _ => h₂)

/-! # Total correctness variants for skip, basic, seq -/

/-- Total skip: skip always terminates. -/
theorem total_hoare_skip (P : Unit → σ → Prop) :
    totalHoare (P ()) NondetM.skip P := by
  constructor
  · exact hoare_skip P
  · intro s₀ _
    exact ⟨(), s₀, rfl⟩

/-- Total basic: basic always terminates. -/
theorem total_hoare_basic (f : σ → σ) (Q : Unit → σ → Prop) :
    totalHoare (fun s => Q () (f s)) (NondetM.basic f) Q := by
  constructor
  · exact hoare_basic f Q
  · intro s₀ _
    exact ⟨(), f s₀, rfl⟩

/-- Total seq: if both parts totally terminate, the sequence does too. -/
theorem total_hoare_seq {P : σ → Prop} {R : Unit → σ → Prop} {Q : α → σ → Prop}
    {m₁ : NondetM σ Unit} {m₂ : NondetM σ α}
    (h₁ : totalHoare P m₁ R)
    (h₂ : ∀ u, totalHoare (R u) m₂ Q) :
    totalHoare P (NondetM.seq m₁ m₂) Q := by
  have h₁_valid := h₁.1
  have h₁_term := h₁.2
  constructor
  · exact hoare_seq h₁_valid (fun u => (h₂ u).1)
  · intro s₀ h_pre
    obtain ⟨u, s', h_mem₁⟩ := h₁_term s₀ h_pre
    have h_R := (h₁_valid s₀ h_pre).2 u s' h_mem₁
    obtain ⟨r, s₁, h_mem₂⟩ := (h₂ u).2 s' h_R
    exact ⟨r, s₁, by simp [NondetM.seq, NondetM.bind]; exact ⟨u, s', h_mem₁, h_mem₂⟩⟩

end SkipBasicSeq

/-! # Conditional rules -/

section Cond

variable {σ α : Type}

/-- Cond rule: if both branches satisfy the postcondition under the appropriate guard. -/
theorem hoare_cond {P : σ → Prop} {Q : α → σ → Prop}
    {c : σ → Bool} {t e : NondetM σ α}
    (h_true : validHoare (fun s => P s ∧ c s = true) t Q)
    (h_false : validHoare (fun s => P s ∧ c s = false) e Q) :
    validHoare P (NondetM.cond c t e) Q := by
  intro s₀ h_pre
  cases hc : c s₀ with
  | false =>
    simp [NondetM.cond, hc]
    exact h_false s₀ ⟨h_pre, hc⟩
  | true =>
    simp [NondetM.cond, hc]
    exact h_true s₀ ⟨h_pre, hc⟩

/-- Total cond: if both branches totally terminate. -/
theorem total_hoare_cond {P : σ → Prop} {Q : α → σ → Prop}
    {c : σ → Bool} {t e : NondetM σ α}
    (h_true : totalHoare (fun s => P s ∧ c s = true) t Q)
    (h_false : totalHoare (fun s => P s ∧ c s = false) e Q) :
    totalHoare P (NondetM.cond c t e) Q := by
  constructor
  · exact hoare_cond h_true.1 h_false.1
  · intro s₀ h_pre
    cases hc : c s₀ with
    | false =>
      simp [NondetM.cond, hc]
      exact h_false.2 s₀ ⟨h_pre, hc⟩
    | true =>
      simp [NondetM.cond, hc]
      exact h_true.2 s₀ ⟨h_pre, hc⟩

end Cond

/-! # While loop rules -/

section While

variable {σ : Type}

/-- While-invariant rule (partial correctness).
    If the body preserves the invariant when the condition holds,
    then after the loop, the invariant holds and the condition is false. -/
theorem hoare_while {I : σ → Prop} {c : σ → Bool} {body : NondetM σ Unit}
    (h_body : validHoare (fun s => I s ∧ c s = true) body (fun _ s => I s)) :
    validHoare I (NondetM.whileLoop c body) (fun _ s => I s ∧ c s = false) := by
  intro s₀ h_inv
  -- Key lemma: invariant is preserved along any WhileResult chain
  have inv_preserved : ∀ s s', NondetM.WhileResult c body s s' → I s → I s' := by
    intro s s' h_result h_I
    induction h_result with
    | done _ _ => exact h_I
    | step s t s' hc h_mem _h_rest ih =>
      have ⟨_, h_post⟩ := h_body s ⟨h_I, hc⟩
      exact ih (h_post () t h_mem)
  -- Key lemma: no failure along any chain where invariant holds
  have no_fail : ∀ s, I s → ¬ NondetM.WhileFail c body s := by
    intro s h_I h_fail
    induction h_fail with
    | here s hc h_body_fail =>
      exact (h_body s ⟨h_I, hc⟩).1 h_body_fail
    | later s t hc h_mem _h_rest ih =>
      have h_I_t := (h_body s ⟨h_I, hc⟩).2 () t h_mem
      exact ih h_I_t
  -- Key lemma: condition is false at the end of any result chain
  have cond_false : ∀ s s', NondetM.WhileResult c body s s' → c s' = false := by
    intro s s' h_result
    induction h_result with
    | done _ hc => exact hc
    | step _ _ _ _ _ _ ih => exact ih
  constructor
  · exact no_fail s₀ h_inv
  · intro r s₁ h_mem
    have h_result : NondetM.WhileResult c body s₀ s₁ := h_mem
    exact ⟨inv_preserved s₀ s₁ h_result h_inv, cond_false s₀ s₁ h_result⟩

/-- While-invariant + variant rule (total correctness).
    Requires a well-founded measure that strictly decreases on each iteration. -/
theorem hoare_while_total {I : σ → Prop} {c : σ → Bool}
    {body : NondetM σ Unit} {variant : σ → Nat}
    (h_body : totalHoare (fun s => I s ∧ c s = true) body (fun _ s => I s))
    (h_variant : ∀ s, I s → c s = true →
      ∀ s', ((), s') ∈ (body s).results → variant s' < variant s) :
    totalHoare I (NondetM.whileLoop c body) (fun _ s => I s ∧ c s = false) := by
  constructor
  · exact hoare_while h_body.1
  · -- termination: produce at least one result
    intro s₀ h_inv
    -- Strong induction on variant
    suffices h : ∀ (n : Nat) (s : σ), I s → variant s ≤ n →
        ∃ s', NondetM.WhileResult c body s s' by
      obtain ⟨s', h_result⟩ := h (variant s₀) s₀ h_inv (Nat.le_refl _)
      exact ⟨(), s', h_result⟩
    intro n
    induction n with
    | zero =>
      intro s h_I h_le
      cases hc : c s with
      | false => exact ⟨s, NondetM.WhileResult.done s hc⟩
      | true =>
        -- variant = 0, condition true, body decreases → contradiction
        obtain ⟨_, s', h_mem⟩ := h_body.2 s ⟨h_I, hc⟩
        have := h_variant s h_I hc s' h_mem
        omega
    | succ k ih =>
      intro s h_I h_le
      cases hc : c s with
      | false => exact ⟨s, NondetM.WhileResult.done s hc⟩
      | true =>
        -- Execute body once
        obtain ⟨_, s', h_mem⟩ := h_body.2 s ⟨h_I, hc⟩
        have h_I' := (h_body.1 s ⟨h_I, hc⟩).2 () s' h_mem
        have h_dec := h_variant s h_I hc s' h_mem
        -- Recurse: variant decreased
        obtain ⟨s'', h_rest⟩ := ih s' h_I' (by omega)
        exact ⟨s'', NondetM.WhileResult.step s s' s'' hc h_mem h_rest⟩

end While

/-! # Consequence / Structural rules -/

section Consequence

variable {σ α : Type}

/-- Consequence rule (pre-strengthening, post-weakening). -/
theorem hoare_consequence {P P' : σ → Prop} {Q Q' : α → σ → Prop} {m : NondetM σ α}
    (h_pre : ∀ s, P' s → P s)
    (h_post : ∀ r s, Q r s → Q' r s)
    (h : validHoare P m Q) :
    validHoare P' m Q' := by
  intro s₀ h_P'
  have ⟨h_nf, h_post_orig⟩ := h s₀ (h_pre s₀ h_P')
  exact ⟨h_nf, fun r s₁ h_mem => h_post r s₁ (h_post_orig r s₁ h_mem)⟩

/-- Pre-strengthening. -/
theorem hoare_strengthen_pre {P P' : σ → Prop} {Q : α → σ → Prop} {m : NondetM σ α}
    (h_pre : ∀ s, P' s → P s)
    (h : validHoare P m Q) :
    validHoare P' m Q :=
  hoare_consequence h_pre (fun _ _ hq => hq) h

/-- Post-weakening. -/
theorem hoare_weaken_post {P : σ → Prop} {Q Q' : α → σ → Prop} {m : NondetM σ α}
    (h_post : ∀ r s, Q r s → Q' r s)
    (h : validHoare P m Q) :
    validHoare P m Q' :=
  hoare_consequence (fun _ hp => hp) h_post h

/-- Conjunction rule: if two postconditions hold independently, their conjunction holds. -/
theorem hoare_conj {P : σ → Prop} {Q₁ Q₂ : α → σ → Prop} {m : NondetM σ α}
    (h₁ : validHoare P m Q₁)
    (h₂ : validHoare P m Q₂) :
    validHoare P m (fun r s => Q₁ r s ∧ Q₂ r s) := by
  intro s₀ h_P
  have ⟨h_nf₁, h_post₁⟩ := h₁ s₀ h_P
  have ⟨_, h_post₂⟩ := h₂ s₀ h_P
  exact ⟨h_nf₁, fun r s₁ h_mem => ⟨h_post₁ r s₁ h_mem, h_post₂ r s₁ h_mem⟩⟩

/-- Frame rule for NondetM.
    For a flat state monad (no separation logic), the frame rule says:
    if m satisfies {P} m {Q} and also preserves R, then
    {P /\ R} m {Q /\ R}.

    This is the conjunction rule applied with an R-preserving hypothesis.
    The true separation logic frame rule (with separating conjunction)
    comes in Phase 3 with HeapLift.

    Alternative formulation: given that m preserves R under precondition P,
    we can add R to both pre and postcondition. -/
theorem hoare_frame {P : σ → Prop} {Q : α → σ → Prop} {R : σ → Prop}
    {m : NondetM σ α}
    (h : validHoare P m Q)
    (h_R : validHoare P m (fun _ s => R s)) :
    validHoare P m (fun r s => Q r s ∧ R s) :=
  hoare_conj h h_R

/-- Total consequence rule. -/
theorem total_hoare_consequence {P P' : σ → Prop} {Q Q' : α → σ → Prop} {m : NondetM σ α}
    (h_pre : ∀ s, P' s → P s)
    (h_post : ∀ r s, Q r s → Q' r s)
    (h : totalHoare P m Q) :
    totalHoare P' m Q' := by
  constructor
  · exact hoare_consequence h_pre h_post h.1
  · intro s₀ h_P'
    exact h.2 s₀ (h_pre s₀ h_P')

end Consequence

/-! # Bind rule (general monadic sequencing) -/

section Bind

variable {σ α β : Type}

/-- Bind rule: general monadic sequencing, handling return values. -/
theorem hoare_bind {P : σ → Prop} {Q : α → σ → Prop} {R : β → σ → Prop}
    {m : NondetM σ α} {f : α → NondetM σ β}
    (h₁ : validHoare P m Q)
    (h₂ : ∀ a, validHoare (Q a) (f a) R) :
    validHoare P (m >>= f) R := by
  intro s₀ h_pre
  have ⟨h_nf₁, h_post₁⟩ := h₁ s₀ h_pre
  constructor
  · intro h_fail
    rcases h_fail with h_fail₁ | ⟨a, s', h_mem, h_fail₂⟩
    · exact h_nf₁ h_fail₁
    · exact (h₂ a s' (h_post₁ a s' h_mem)).1 h_fail₂
  · intro r s₁ h_mem
    obtain ⟨a, s', h_mem₁, h_mem₂⟩ := h_mem
    exact (h₂ a s' (h_post₁ a s' h_mem₁)).2 r s₁ h_mem₂

end Bind
