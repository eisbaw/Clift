-- L1 Hoare rules: validHoare rules for L1 combinators
--
-- These rules let us prove validHoare for L1 monadic computations
-- compositionally, avoiding deep kernel term nesting.
--
-- L1 combinators (L1.guard, L1.modify, L1.seq, L1.catch, L1.skip)
-- operate on NondetM σ (Except Unit Unit). These rules are specific
-- to that return type.
--
-- The guard/modify result lemmas use `show` + `if_pos` instead of `simp`
-- to produce small proof terms that avoid kernel deep recursion.

import Clift.Lifting.SimplConv
import Clift.MonadLib.Hoare

set_option maxHeartbeats 800000

/-! # L1 low-level result lemmas

These lemmas characterize L1 combinator results without deep proof terms.
The key technique: use `show` to expose the `if` expression inside L1.guard,
then `rw [if_pos]` to evaluate it. This avoids `simp` which generates deep terms. -/

section L1Results

variable {σ : Type}

/-- L1.guard does not fail when the predicate holds. -/
theorem L1_guard_not_failed {p : σ → Prop} [DecidablePred p] {s : σ}
    (hp : p s) : ¬(L1.guard p s).failed := by
  show ¬(if p s then (⟨{(Except.ok (), s)}, False⟩ : NondetResult σ (Except Unit Unit))
         else ⟨∅, True⟩).failed
  rw [if_pos hp]; exact not_false

/-- L1.guard produces exactly {(ok, s)} when the predicate holds. -/
theorem L1_guard_results {p : σ → Prop} [DecidablePred p] {s : σ}
    (hp : p s) : (L1.guard p s).results = {(Except.ok (), s)} := by
  show (if p s then (⟨{(Except.ok (), s)}, False⟩ : NondetResult σ (Except Unit Unit))
       else ⟨∅, True⟩).results = _
  rw [if_pos hp]

/-- L1.guard never produces error results when the predicate holds. -/
theorem L1_guard_no_error {p : σ → Prop} [DecidablePred p] {s s' : σ}
    (hp : p s) : (Except.error (), s') ∉ (L1.guard p s).results := by
  rw [L1_guard_results hp]
  intro h; exact absurd (Prod.mk.inj h).1 (by intro h; cases h)

/-- L1.seq (guard p) (modify f) produces exactly {(ok, f s)} when p holds.
    This is the workhorse lemma for swap verification: it characterizes the
    result of a guard+modify pair without deep term nesting. -/
theorem L1_guard_modify_result (p : σ → Prop) [DecidablePred p] (f : σ → σ) (s : σ)
    (hp : p s) :
    (L1.seq (L1.guard p) (L1.modify f) s).results = {(Except.ok (), f s)} ∧
    ¬(L1.seq (L1.guard p) (L1.modify f) s).failed := by
  constructor
  · ext ⟨r, s'⟩; constructor
    · intro h; change (_ ∨ _) at h
      rcases h with ⟨s'', h_g, h_m⟩ | ⟨h_e, _⟩
      · rw [L1_guard_results hp] at h_g
        have ⟨_, rfl⟩ := Prod.mk.inj h_g; exact h_m
      · exact absurd h_e (L1_guard_no_error hp)
    · intro h; change (_ ∨ _); left
      exact ⟨s, by rw [L1_guard_results hp]; rfl, h⟩
  · intro hf; change (_ ∨ _) at hf
    rcases hf with h1 | ⟨s', _, h2⟩
    · exact L1_guard_not_failed hp h1
    · exact h2

/-- L1.seq (guard p) (seq (guard q) (modify f)) produces {(ok, f s)}. -/
theorem L1_guard_guard_modify_result (p q : σ → Prop) [DecidablePred p] [DecidablePred q]
    (f : σ → σ) (s : σ) (hp : p s) (hq : q s) :
    (L1.seq (L1.guard p) (L1.seq (L1.guard q) (L1.modify f)) s).results =
      {(Except.ok (), f s)} ∧
    ¬(L1.seq (L1.guard p) (L1.seq (L1.guard q) (L1.modify f)) s).failed := by
  have h_inner := L1_guard_modify_result q f s hq
  constructor
  · ext ⟨r, s'⟩; constructor
    · intro h; change (_ ∨ _) at h
      rcases h with ⟨s'', h_g, h_m⟩ | ⟨h_e, _⟩
      · rw [L1_guard_results hp] at h_g
        have ⟨_, rfl⟩ := Prod.mk.inj h_g
        rw [h_inner.1] at h_m; exact h_m
      · exact absurd h_e (L1_guard_no_error hp)
    · intro h; change (_ ∨ _); left
      exact ⟨s, by rw [L1_guard_results hp]; rfl, by rw [h_inner.1]; exact h⟩
  · intro hf; change (_ ∨ _) at hf
    rcases hf with h1 | ⟨s', h_mem, h2⟩
    · exact L1_guard_not_failed hp h1
    · rw [L1_guard_results hp] at h_mem
      have ⟨_, rfl⟩ := Prod.mk.inj h_mem
      exact h_inner.2 h2

/-- When m₁ produces exactly one ok result at s₁, L1.seq m₁ m₂ has the
    same results and failure as m₂ at s₁. -/
theorem L1_seq_singleton_ok {m₁ m₂ : L1Monad σ} {s s₁ : σ}
    (h_res : (m₁ s).results = {(Except.ok (), s₁)})
    (h_nf : ¬(m₁ s).failed) :
    (L1.seq m₁ m₂ s).results = (m₂ s₁).results ∧
    ((L1.seq m₁ m₂ s).failed ↔ (m₂ s₁).failed) := by
  constructor
  · ext ⟨r, s'⟩; constructor
    · intro h; change (_ ∨ _) at h
      rcases h with ⟨s'', h_m1, h_m2⟩ | ⟨h_e, _⟩
      · rw [h_res] at h_m1
        have ⟨_, rfl⟩ := Prod.mk.inj h_m1; exact h_m2
      · rw [h_res] at h_e
        exact absurd (Prod.mk.inj h_e).1 (by intro h; cases h)
    · intro h; change (_ ∨ _); left
      exact ⟨s₁, by rw [h_res]; rfl, h⟩
  · constructor
    · intro hf; change (_ ∨ _) at hf
      rcases hf with h1 | ⟨s', h_mem, h2⟩
      · exact absurd h1 h_nf
      · rw [h_res] at h_mem
        have ⟨_, rfl⟩ := Prod.mk.inj h_mem; exact h2
    · intro hf; change (_ ∨ _); right
      exact ⟨s₁, by rw [h_res]; rfl, hf⟩

/-- When the body produces exactly one ok result, catch body skip = {(ok, s')}. -/
theorem L1_catch_singleton_ok {body : L1Monad σ} {s s' : σ}
    (h_res : (body s).results = {(Except.ok (), s')})
    (h_nf : ¬(body s).failed) :
    (L1.catch body L1.skip s).results = {(Except.ok (), s')} ∧
    ¬(L1.catch body L1.skip s).failed := by
  constructor
  · ext ⟨r, s''⟩; constructor
    · intro h; change (_ ∨ _) at h
      rcases h with ⟨h_ok, rfl⟩ | ⟨s₁, h_err, _⟩
      · rw [h_res] at h_ok; exact h_ok
      · rw [h_res] at h_err
        exact absurd (Prod.mk.inj h_err).1 (by intro h; cases h)
    · intro h; change (_ ∨ _); left
      have heq := Prod.mk.inj h
      constructor
      · show (Except.ok (), (r, s'').2) ∈ (body s).results
        rw [h_res]; rw [heq.2]; rfl
      · exact heq.1
  · intro hf; change (_ ∨ _) at hf
    rcases hf with h1 | ⟨s₁, h_err, _⟩
    · exact h_nf h1
    · rw [h_res] at h_err
      exact absurd (Prod.mk.inj h_err).1 (by intro h; cases h)

end L1Results
