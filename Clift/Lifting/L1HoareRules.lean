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

/-- seq (modify f) throw produces exactly {(error, f s)}, not failed. -/
theorem L1_modify_throw_result (f : σ → σ) (s : σ) :
    (L1.seq (L1.modify f) L1.throw s).results = {(Except.error (), f s)} ∧
    ¬(L1.seq (L1.modify f) L1.throw s).failed := by
  constructor
  · ext ⟨r, s'⟩; constructor
    · intro h; change (_ ∨ _) at h
      rcases h with ⟨s'', h_mod, h_throw⟩ | ⟨h_err, _⟩
      · have ⟨_, rfl⟩ := Prod.mk.inj h_mod
        exact h_throw
      · exact absurd (Prod.mk.inj h_err).1 (by intro h; cases h)
    · intro h; change (_ ∨ _); left
      refine ⟨f s, rfl, ?_⟩; rw [h]; show (Except.error (), f s) ∈ {(Except.error (), f s)}; rfl
  · intro hf; change (_ ∨ _) at hf
    rcases hf with h | ⟨_, _, h⟩ <;> exact h

/-- catch body skip: when body produces exactly {(error, s')}, result is {(ok, s')}. -/
theorem L1_catch_error_singleton {body : L1Monad σ} {s s' : σ}
    (h_res : (body s).results = {(Except.error (), s')})
    (h_nf : ¬(body s).failed) :
    (L1.catch body L1.skip s).results = {(Except.ok (), s')} ∧
    ¬(L1.catch body L1.skip s).failed := by
  constructor
  · ext ⟨r, t⟩; constructor
    · intro h; change (_ ∨ _) at h
      rcases h with ⟨h_ok, _⟩ | ⟨s'', h_err, h_skip⟩
      · rw [h_res] at h_ok; exact absurd (Prod.mk.inj h_ok).1 (by intro h; cases h)
      · rw [h_res] at h_err
        have ⟨_, rfl⟩ := Prod.mk.inj h_err
        exact h_skip
    · intro h; change (_ ∨ _); right
      refine ⟨s', ?_, h⟩; rw [h_res]; simp only [Set.mem_singleton_iff]
  · intro hf; change (_ ∨ _) at hf
    rcases hf with hf1 | ⟨s'', h_err, hf2⟩
    · exact h_nf hf1
    · exact hf2

/-- When m1 produces exactly one error result, seq m1 m2 propagates that error. -/
theorem L1_seq_error_propagate {m₁ m₂ : L1Monad σ} {s s' : σ}
    (h_res : (m₁ s).results = {(Except.error (), s')})
    (h_nf : ¬(m₁ s).failed) :
    (L1.seq m₁ m₂ s).results = {(Except.error (), s')} ∧
    ¬(L1.seq m₁ m₂ s).failed := by
  constructor
  · ext ⟨r, t⟩; constructor
    · intro h; change (_ ∨ _) at h
      rcases h with ⟨t', h_ok, _⟩ | ⟨h_err, h_eq⟩
      · rw [h_res] at h_ok; exact absurd (Prod.mk.inj h_ok).1 (by intro h; cases h)
      · rw [h_res] at h_err; have ⟨_, ht⟩ := Prod.mk.inj h_err
        exact Prod.ext h_eq ht
    · intro h; change (_ ∨ _); right
      have ⟨hr, ht⟩ := Prod.mk.inj h
      constructor
      · show (Except.error (), t) ∈ (m₁ s).results; rw [h_res, ht]; rfl
      · exact hr
  · intro hf; change (_ ∨ _) at hf
    rcases hf with hf1 | ⟨t', h_ok, _⟩
    · exact h_nf hf1
    · rw [h_res] at h_ok; exact absurd (Prod.mk.inj h_ok).1 (by intro h; cases h)

/-- The modify-throw-catch-skip pattern: pure, returns with f applied. -/
theorem L1_modify_throw_catch_skip_result (f : σ → σ) (s : σ) :
    (L1.catch (L1.seq (L1.modify f) L1.throw) L1.skip s).results =
      {(Except.ok (), f s)} ∧
    ¬(L1.catch (L1.seq (L1.modify f) L1.throw) L1.skip s).failed :=
  let ⟨h1, h2⟩ := L1_modify_throw_result f s
  L1_catch_error_singleton h1 h2

/-- The guard-modify-throw-catch-skip pattern: reads heap, sets ret__val, returns. -/
theorem L1_guard_modify_throw_catch_skip_result
    (p : σ → Prop) [DecidablePred p] (f : σ → σ) (s : σ) (hp : p s) :
    (L1.catch (L1.seq (L1.guard p) (L1.seq (L1.modify f) L1.throw)) L1.skip s).results =
      {(Except.ok (), f s)} ∧
    ¬(L1.catch (L1.seq (L1.guard p) (L1.seq (L1.modify f) L1.throw)) L1.skip s).failed := by
  have h_seq := L1_seq_singleton_ok (L1_guard_results hp) (L1_guard_not_failed hp)
    (m₂ := L1.seq (L1.modify f) L1.throw)
  have ⟨h_mt_res, h_mt_nf⟩ := L1_modify_throw_result f s
  have h_body_res : (L1.seq (L1.guard p) (L1.seq (L1.modify f) L1.throw) s).results =
      {(Except.error (), f s)} := by rw [h_seq.1, h_mt_res]
  have h_body_nf : ¬(L1.seq (L1.guard p) (L1.seq (L1.modify f) L1.throw) s).failed :=
    fun hf => h_mt_nf (h_seq.2.mp hf)
  exact L1_catch_error_singleton h_body_res h_body_nf

end L1Results

/-! # L1 Hoare rules (validHoare)

These theorems let us prove `validHoare` for L1 monadic programs compositionally.
Each rule handles one L1 combinator and produces small proof obligations. -/

section L1Hoare

variable {σ : Type}

/-- L1.skip satisfies any postcondition that holds for ok in the initial state. -/
theorem L1_hoare_skip (Q : Except Unit Unit → σ → Prop) :
    validHoare (fun s => Q (Except.ok ()) s) L1.skip Q := by
  intro s₀ hpre
  constructor
  · intro h; exact h  -- L1.skip = NondetM.pure, failed = False
  · intro r s₁ h_mem
    -- L1.skip s = NondetM.pure (ok ()), so results = {(ok (), s)}
    have heq := (Prod.mk.inj h_mem)
    rw [heq.1, heq.2]; exact hpre

/-- L1.modify f: precondition must ensure Q holds at f s. -/
theorem L1_hoare_modify (f : σ → σ) (Q : Except Unit Unit → σ → Prop) :
    validHoare (fun s => Q (Except.ok ()) (f s)) (L1.modify f) Q := by
  intro s₀ hpre
  constructor
  · intro h; exact h  -- L1.modify failed = False
  · intro r s₁ h_mem
    -- L1.modify f s = {(ok (), f s)}
    have heq := (Prod.mk.inj h_mem)
    rw [heq.1, heq.2]; exact hpre

/-- L1.guard p: precondition must ensure p holds and Q holds at s. -/
theorem L1_hoare_guard (p : σ → Prop) [DecidablePred p] (Q : Except Unit Unit → σ → Prop) :
    validHoare (fun s => p s ∧ Q (Except.ok ()) s) (L1.guard p) Q := by
  intro s₀ ⟨hp, hq⟩
  constructor
  · exact L1_guard_not_failed hp
  · intro r s₁ h_mem
    rw [L1_guard_results hp] at h_mem
    have heq := (Prod.mk.inj h_mem)
    rw [heq.1, heq.2]; exact hq

/-- L1.seq: sequential composition with intermediate condition R.
    m₁ must establish R on ok results, and propagate Q on error results.
    m₂ from R must establish Q. -/
theorem L1_hoare_seq (P : σ → Prop) (R : σ → Prop) (Q : Except Unit Unit → σ → Prop)
    (m₁ m₂ : L1Monad σ)
    (h1 : validHoare P m₁ (fun r s => match r with | Except.ok () => R s | Except.error () => Q (Except.error ()) s))
    (h2 : validHoare R m₂ Q) :
    validHoare P (L1.seq m₁ m₂) Q := by
  intro s₀ hpre
  have ⟨h1_nf, h1_post⟩ := h1 s₀ hpre
  constructor
  · -- no failure
    intro hf
    change (_ ∨ _) at hf
    rcases hf with hf1 | ⟨s', h_mem, hf2⟩
    · exact h1_nf hf1
    · have h_R := h1_post (Except.ok ()) s' h_mem
      exact (h2 s' h_R).1 hf2
  · -- postcondition
    intro r s₁ h_mem
    change (_ ∨ _) at h_mem
    rcases h_mem with ⟨s', h_m1, h_m2⟩ | ⟨h_err, h_eq⟩
    · have h_R := h1_post (Except.ok ()) s' h_m1
      exact (h2 s' h_R).2 r s₁ h_m2
    · have h_Q := h1_post (Except.error ()) s₁ h_err
      have : r = Except.error () := h_eq
      rw [this]; exact h_Q

/-- L1.catch: body ok results pass through, body error results go to handler.
    R is the intermediate condition for error states entering the handler. -/
theorem L1_hoare_catch (P : σ → Prop) (R : σ → Prop) (Q : Except Unit Unit → σ → Prop)
    (body handler : L1Monad σ)
    (h_body : validHoare P body (fun r s => match r with
      | Except.ok () => Q (Except.ok ()) s
      | Except.error () => R s))
    (h_handler : validHoare R handler Q) :
    validHoare P (L1.catch body handler) Q := by
  intro s₀ hpre
  have ⟨hb_nf, hb_post⟩ := h_body s₀ hpre
  constructor
  · -- no failure
    intro hf
    change (_ ∨ _) at hf
    rcases hf with hf1 | ⟨s', h_err, hf2⟩
    · exact hb_nf hf1
    · have h_R := hb_post (Except.error ()) s' h_err
      exact (h_handler s' h_R).1 hf2
  · -- postcondition
    intro r s₁ h_mem
    change (_ ∨ _) at h_mem
    rcases h_mem with ⟨h_ok, h_eq⟩ | ⟨s', h_err, h_handler_mem⟩
    · -- ok from body passes through
      have : r = Except.ok () := h_eq
      rw [this]
      have h_Q := hb_post (Except.ok ()) s₁ h_ok
      exact h_Q
    · -- error from body goes to handler
      have h_R := hb_post (Except.error ()) s' h_err
      exact (h_handler s' h_R).2 r s₁ h_handler_mem

/-- Simplified seq rule for ok-only first monad.
    When m₁ only produces ok results (like guard, modify, skip),
    the error propagation in L1.seq is vacuous.
    This avoids the nested match problem. -/
theorem L1_hoare_seq_ok (P : σ → Prop) (R : σ → Prop) (Q : Except Unit Unit → σ → Prop)
    (m₁ m₂ : L1Monad σ)
    (h1 : validHoare P m₁ (fun r s => r = Except.ok () ∧ R s))
    (h2 : validHoare R m₂ Q) :
    validHoare P (L1.seq m₁ m₂) Q := by
  intro s₀ hpre
  have ⟨h1_nf, h1_post⟩ := h1 s₀ hpre
  constructor
  · intro hf
    change (_ ∨ _) at hf
    rcases hf with hf1 | ⟨s', h_mem, hf2⟩
    · exact h1_nf hf1
    · exact (h2 s' (h1_post _ s' h_mem).2).1 hf2
  · intro r s₁ h_mem
    change (_ ∨ _) at h_mem
    rcases h_mem with ⟨s', h_m1, h_m2⟩ | ⟨h_err, h_eq⟩
    · exact (h2 s' (h1_post _ s' h_m1).2).2 r s₁ h_m2
    · -- error from m₁: but m₁ only produces ok, contradiction
      -- h_err : (Except.error (), (r, s₁).snd) ∈ results
      -- h_eq : (r, s₁).fst = Except.error ()
      have h_post := h1_post (Except.error ()) (r, s₁).snd h_err
      exact absurd h_post.1 (by intro h; cases h)

/-- Guard Hoare rule producing r = ok ∧ R form. -/
theorem L1_hoare_guard' (p : σ → Prop) [DecidablePred p] (R : σ → Prop) :
    validHoare (fun s => p s ∧ R s) (L1.guard p)
      (fun r s => r = Except.ok () ∧ R s) := by
  intro s₀ ⟨hp, hr⟩
  constructor
  · exact L1_guard_not_failed hp
  · intro r s₁ h_mem
    rw [L1_guard_results hp] at h_mem
    have heq := Prod.mk.inj h_mem
    exact ⟨heq.1, heq.2 ▸ hr⟩

/-- Modify Hoare rule producing r = ok ∧ R form. -/
theorem L1_hoare_modify' (f : σ → σ) (R : σ → Prop) :
    validHoare (fun s => R (f s)) (L1.modify f)
      (fun r s => r = Except.ok () ∧ R s) := by
  intro s₀ hpre
  constructor
  · intro h; exact h
  · intro r s₁ h_mem
    have heq := Prod.mk.inj h_mem
    exact ⟨heq.1, heq.2 ▸ hpre⟩

/-- Catch rule for ok-only body: when body only produces ok results,
    the handler is never invoked, and the postcondition passes through. -/
theorem L1_hoare_catch_ok (P : σ → Prop) (Q : Except Unit Unit → σ → Prop)
    (body handler : L1Monad σ)
    (h_body : validHoare P body (fun r s => r = Except.ok () ∧ Q (Except.ok ()) s)) :
    validHoare P (L1.catch body handler) Q := by
  intro s₀ hpre
  have ⟨hb_nf, hb_post⟩ := h_body s₀ hpre
  constructor
  · intro hf
    change (_ ∨ _) at hf
    rcases hf with hf1 | ⟨s', h_err, _⟩
    · exact hb_nf hf1
    · have hp := hb_post (Except.error ()) s' h_err
      exact absurd hp.1 (by intro h; cases h)
  · intro r s₁ h_mem
    change (_ ∨ _) at h_mem
    rcases h_mem with ⟨h_ok, h_eq⟩ | ⟨s', h_err, _⟩
    · -- h_ok : (Except.ok (), (r, s₁).snd) ∈ results
      -- h_eq : (r, s₁).fst = Except.ok ()
      have hp := hb_post (Except.ok ()) (r, s₁).snd h_ok
      subst h_eq; exact hp.2
    · have hp := hb_post (Except.error ()) s' h_err
      exact absurd hp.1 (by intro h; cases h)

/-- Pre-strengthening for validHoare. -/
theorem L1_hoare_pre {P P' : σ → Prop} {Q : Except Unit Unit → σ → Prop}
    {m : L1Monad σ}
    (h_pre : ∀ s, P' s → P s)
    (h : validHoare P m Q) :
    validHoare P' m Q :=
  fun s hp => h s (h_pre s hp)

/-! ## L1 while loop Hoare rule

The key theorem that enables verification of loop-containing C functions.
Given a loop invariant I, proves validHoare for L1.while by:
1. Showing WhileFail cannot happen (body doesn't fail when I holds + condition true)
2. Showing every WhileResult satisfies Q (by induction on the derivation)

The invariant I must:
- Be established by the precondition P
- Be preserved by the loop body (when condition is true and body returns ok)
- Imply Q when the loop exits (condition is false → Q(ok, s))
- The body's abrupt (error) results must also satisfy Q
-/

-- Generalized: WhileFail is impossible when invariant holds
private theorem L1_while_not_failed_of_inv {σ : Type} {c : σ → Bool} {body : L1Monad σ}
    {I : σ → Prop}
    (h_body_nf : ∀ s, I s → c s = true → ¬(body s).failed)
    (h_body_inv : ∀ s s', I s → c s = true → (Except.ok (), s') ∈ (body s).results → I s')
    : ∀ s, I s → ¬L1.WhileFail c body s := by
  intro s h_I h_fail
  induction h_fail with
  | here s' hc hf => exact h_body_nf s' h_I hc hf
  | later s' s'' hc h_body h_rest ih =>
    exact ih (h_body_inv s' s'' h_I hc h_body)

-- Generalized: every WhileResult satisfies Q when invariant holds
private theorem L1_while_result_of_inv {σ : Type} {c : σ → Bool} {body : L1Monad σ}
    {I : σ → Prop} {Q : Except Unit Unit → σ → Prop}
    (h_body_inv : ∀ s s', I s → c s = true → (Except.ok (), s') ∈ (body s).results → I s')
    (h_exit : ∀ s, I s → c s = false → Q (Except.ok ()) s)
    (h_abrupt : ∀ s s', I s → c s = true → (Except.error (), s') ∈ (body s).results →
                Q (Except.error ()) s')
    : ∀ s (p : Except Unit Unit × σ), I s → L1.WhileResult c body s p → Q p.1 p.2 := by
  intro s p h_I h_wr
  induction h_wr with
  | done s₀ hc => exact h_exit s₀ h_I hc
  | step s₀ s₁ _ hc h_body _ ih => exact ih (h_body_inv s₀ s₁ h_I hc h_body)
  | abrupt s₀ s₁ hc h_body => exact h_abrupt s₀ s₁ h_I hc h_body

theorem L1_hoare_while {σ : Type} {c : σ → Bool} {body : L1Monad σ}
    {P : σ → Prop} {Q : Except Unit Unit → σ → Prop}
    (I : σ → Prop)
    -- Initialization: P implies I
    (h_init : ∀ s, P s → I s)
    -- Body doesn't fail when invariant holds and condition is true
    (h_body_nf : ∀ s, I s → c s = true → ¬(body s).failed)
    -- Body preserves invariant on normal (ok) return
    (h_body_inv : ∀ s s', I s → c s = true → (Except.ok (), s') ∈ (body s).results → I s')
    -- Exit condition: invariant + condition false implies postcondition
    (h_exit : ∀ s, I s → c s = false → Q (Except.ok ()) s)
    -- Abrupt exit: body error results satisfy Q
    (h_abrupt : ∀ s s', I s → c s = true → (Except.error (), s') ∈ (body s).results →
                Q (Except.error ()) s') :
    validHoare P (L1.while c body) Q := by
  intro s₀ h_P
  have h_I₀ := h_init s₀ h_P
  constructor
  · -- WhileFail is impossible
    exact L1_while_not_failed_of_inv h_body_nf h_body_inv s₀ h_I₀
  · -- Every WhileResult satisfies Q
    intro r s₁ h_mem
    exact L1_while_result_of_inv h_body_inv h_exit h_abrupt s₀ (r, s₁) h_I₀ h_mem

/-- Combined guard+modify Hoare rule.
    When the precondition implies the guard predicate p, and Q holds at (f s),
    then validHoare holds for seq (guard p) (modify f).
    This handles the most common L1 pattern in a single step. -/
theorem L1_hoare_guard_modify (p : σ → Prop) [DecidablePred p] (f : σ → σ)
    (Q : Except Unit Unit → σ → Prop)
    (h : ∀ s, p s → Q (Except.ok ()) (f s)) :
    validHoare (fun s => p s) (L1.seq (L1.guard p) (L1.modify f)) Q := by
  intro s₀ hp
  have h_gm := L1_guard_modify_result p f s₀ hp
  constructor
  · exact h_gm.2
  · intro r s₁ h_mem
    rw [h_gm.1] at h_mem
    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
    rw [hr, hs]; exact h s₀ hp

/-- Combined guard+modify producing r = ok ∧ R form (for seq_ok chains). -/
theorem L1_hoare_guard_modify' (p : σ → Prop) [DecidablePred p] (f : σ → σ) (R : σ → Prop)
    (h : ∀ s, p s → R (f s)) :
    validHoare (fun s => p s) (L1.seq (L1.guard p) (L1.modify f))
      (fun r s => r = Except.ok () ∧ R s) := by
  intro s₀ hp
  have h_gm := L1_guard_modify_result p f s₀ hp
  constructor
  · exact h_gm.2
  · intro r s₁ h_mem
    rw [h_gm.1] at h_mem
    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
    exact ⟨hr, hs ▸ h s₀ hp⟩

/-- Post-weakening: strengthen postcondition from True to any trivially-true Q.
    When the postcondition Q holds for all r and s, and we can prove validHoare P m True,
    then validHoare P m Q follows. Useful when specs have tautological postconditions. -/
theorem L1_hoare_weaken_trivial_post
    {P : σ → Prop} {Q : Except Unit Unit → σ → Prop}
    {m : L1Monad σ}
    (hQ : ∀ r s, Q r s)
    (h : validHoare P m (fun _ _ => True)) :
    validHoare P m Q := by
  intro s₀ hpre
  have ⟨h_nf, _⟩ := h s₀ hpre
  exact ⟨h_nf, fun r s₁ _ => hQ r s₁⟩

/-- L1.condition Hoare rule: when the condition is decidable, prove both branches. -/
theorem L1_hoare_condition (c : σ → Bool) (t e : L1Monad σ)
    (P : σ → Prop) (Q : Except Unit Unit → σ → Prop)
    (h_true : validHoare (fun s => P s ∧ c s = true) t Q)
    (h_false : validHoare (fun s => P s ∧ c s = false) e Q) :
    validHoare P (L1.condition c t e) Q := by
  intro s₀ hpre
  simp only [L1.condition]
  cases hc : c s₀ with
  | false => exact h_false s₀ ⟨hpre, hc⟩
  | true => exact h_true s₀ ⟨hpre, hc⟩

/-- L1.condition Hoare rule with ok-only postcondition (for seq_ok chains). -/
theorem L1_hoare_condition' (c : σ → Bool) (t e : L1Monad σ)
    (P : σ → Prop) (R : σ → Prop)
    (h_true : validHoare (fun s => P s ∧ c s = true) t (fun r s => r = Except.ok () ∧ R s))
    (h_false : validHoare (fun s => P s ∧ c s = false) e (fun r s => r = Except.ok () ∧ R s)) :
    validHoare P (L1.condition c t e) (fun r s => r = Except.ok () ∧ R s) :=
  L1_hoare_condition c t e P _ h_true h_false

end L1Hoare
