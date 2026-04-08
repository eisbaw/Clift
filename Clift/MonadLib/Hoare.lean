-- Hoare triple definitions: validHoare (partial) and totalHoare (total correctness)
--
-- validHoare P m Q: if P holds in the initial state, then m does not fail
--   and every result satisfies Q.
-- totalHoare P m Q: validHoare + at least one result exists (termination).
--
-- These follow plan.md Decision 6 and seL4's valid / validE definitions.

import Clift.MonadLib.NondetM

/-! # Hoare triples for NondetM -/

/-- Partial correctness Hoare triple.
    `validHoare P m Q` means: for every initial state satisfying `P`,
    the computation `m` does not fail, and every (value, state) result satisfies `Q`.

    This is the monadic equivalent of `{P} m {Q}` in Hoare logic. -/
def validHoare {σ α : Type} (P : σ → Prop) (m : NondetM σ α) (Q : α → σ → Prop) : Prop :=
  ∀ s₀, P s₀ →
    ¬(m s₀).failed ∧
    ∀ r s₁, (r, s₁) ∈ (m s₀).results → Q r s₁

/-- Total correctness Hoare triple.
    `totalHoare P m Q` means: partial correctness (validHoare) plus
    the computation must produce at least one result (termination guarantee).

    For nondeterministic computations, "termination" means the result set
    is nonempty -- at least one execution path completes. -/
def totalHoare {σ α : Type} (P : σ → Prop) (m : NondetM σ α) (Q : α → σ → Prop) : Prop :=
  validHoare P m Q ∧
  ∀ s₀, P s₀ → ∃ r s₁, (r, s₁) ∈ (m s₀).results

/-! # Notation -/

-- We avoid custom notation for now to keep things explicit and greppable.
-- Can add `⦃P⦄ m ⦃Q⦄` notation later if needed.

/-! # Basic sanity lemmas -/

/-- Sanity check: `pure x` satisfies `validHoare` with postcondition checking the return value. -/
theorem validHoare_pure {σ α : Type} (x : α) :
    validHoare (fun _ : σ => True) (Pure.pure x : NondetM σ α) (fun r _ => r = x) := by
  intro s₀ _
  constructor
  · -- no failure
    intro h_fail
    exact h_fail
  · -- postcondition
    intro r s₁ h_mem
    have ⟨rfl, _⟩ := Prod.mk.inj h_mem
    rfl

/-- Sanity check: `totalHoare` holds for `pure` as well (it always produces a result). -/
theorem totalHoare_pure {σ α : Type} (x : α) :
    totalHoare (fun _ : σ => True) (Pure.pure x : NondetM σ α) (fun r _ => r = x) := by
  constructor
  · exact validHoare_pure x
  · intro s₀ _
    exact ⟨x, s₀, rfl⟩
