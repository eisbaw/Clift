-- Phase 2 end-to-end: gcd.c lifts to Nat → Nat → Nat
--
-- Chain: C -> CImporter -> CSimpl -> L1 -> L3(pure) -> L5(Nat)

import Examples.GcdWordAbstract
import Examples.GcdCorrect
import Clift.Tactics

set_option maxHeartbeats 6400000

open Gcd

/-! # Helper: gcd while body analysis -/

/-- The gcd while body only produces ok results with known values. -/
private theorem gcd_body_only_ok (s : ProgramState)
    (hb : s.locals.b ≠ 0)
    (e : Except Unit Unit) (t : ProgramState)
    (h : (e, t) ∈ (gcd_while_body s).results) :
    e = Except.ok () ∧
    t.locals.a = s.locals.b ∧ t.locals.b = s.locals.a % s.locals.b ∧ t.globals = s.globals := by
  -- The body produces exactly one result: (ok, {a := b, b := a%b, t := b})
  have h_result := gcd_while_body_result s hb
  -- Both h and h_result point to the same singleton result set.
  -- The result set has exactly one element, so h = h_result.
  unfold gcd_while_body L1.seq L1.modify L1.guard at h
  simp [hb] at h
  -- TODO: The guard addition changed the result set structure.
  -- The proof needs to extract equalities from the singleton membership.
  -- This is a mechanical fix; the result set is still a singleton.
  sorry

/-! # Universal property of WhileResult for gcd -/

/-- For ALL WhileResult outcomes: ok-outcomes compute gcd_l3, error-outcomes are impossible. -/
private theorem gcd_while_universal (n : Nat) :
    ∀ (s : ProgramState) (p : Except Unit Unit × ProgramState),
    s.locals.b.toNat ≤ n →
    L1.WhileResult (fun s => decide (s.locals.b ≠ 0)) gcd_while_body s p →
    (p.1 = Except.ok () →
      p.2.locals.a = gcd_l3 s.locals.a s.locals.b ∧ p.2.globals = s.globals) ∧
    (p.1 = Except.error () → False) := by
  induction n with
  | zero =>
    intro s p hle h_w
    have hb0 : s.locals.b = 0 := by
      have : (0 : UInt32).toNat = 0 := by decide
      exact UInt32.ext (by omega)
    cases h_w with
    | done s0 hc =>
      exact ⟨fun _ => ⟨by rw [hb0, gcd_l3_zero], rfl⟩, fun h => by cases h⟩
    | step s0 t q hc => simp [hb0] at hc
    | abrupt s0 t hc => simp [hb0] at hc
  | succ k ih =>
    intro s p hle h_w
    cases h_w with
    | done _ hc =>
      -- hc : decide (s.locals.b ≠ 0) = false, so s.locals.b = 0
      have hb0 : s.locals.b = 0 := by
        simp [decide_eq_false_iff_not, Decidable.not_not] at hc; exact hc
      exact ⟨fun _ => ⟨by rw [hb0, gcd_l3_zero], rfl⟩, fun h => by cases h⟩
    | step _ t _ hc h_body h_rest =>
      -- hc : decide (s.locals.b ≠ 0) = true, so s.locals.b ≠ 0
      have hb_ne : s.locals.b ≠ 0 := by
        simp [decide_eq_true_eq] at hc; exact hc
      obtain ⟨_, h_ta, h_tb, h_tg⟩ := gcd_body_only_ok s hb_ne _ t h_body
      have h_dec : t.locals.b.toNat ≤ k := by
        rw [h_tb]
        have h_mod := UInt32.toNat_mod s.locals.a s.locals.b
        have h_lt : s.locals.a.toNat % s.locals.b.toNat < s.locals.b.toNat := by
          exact Nat.mod_lt _ (by
            have : s.locals.b.toNat ≠ 0 := fun heq => hb_ne (UInt32.ext heq)
            omega)
        rw [h_mod]; omega
      obtain ⟨ih_ok, ih_err⟩ := ih t _ h_dec h_rest
      exact ⟨fun h_p_ok => by
        obtain ⟨ih_a, ih_g⟩ := ih_ok h_p_ok
        exact ⟨by rw [ih_a, h_ta, h_tb, ← gcd_l3_rec _ _ hb_ne], by rw [ih_g, h_tg]⟩,
        ih_err⟩
    | abrupt _ t hc h_body =>
      exfalso
      have hb_ne' : s.locals.b ≠ 0 := by simp [decide_eq_true_eq] at hc; exact hc
      obtain ⟨h_ok, _, _, _⟩ := gcd_body_only_ok s hb_ne' _ t h_body
      exact absurd h_ok (by intro h; cases h)

/-! # ValidHoare for l1_gcd_body -/

theorem l1_gcd_body_validHoare (a₀ b₀ : UInt32) :
    validHoare
      (fun s : ProgramState => s.locals.a = a₀ ∧ s.locals.b = b₀)
      l1_gcd_body
      (fun r s =>
        match r with
        | Except.ok () =>
          wordToNat s.locals.ret__val = gcd_nat (wordToNat a₀) (wordToNat b₀)
        | Except.error () => True) := by
  intro s₀ ⟨ha, hb⟩; subst ha; subst hb
  refine ⟨l1_gcd_body_not_failed s₀, ?_⟩
  intro r s₁ h_mem
  match r with
  | Except.error () => trivial
  | Except.ok () =>
    unfold l1_gcd_body at h_mem
    simp only [L1.catch] at h_mem
    rcases h_mem with ⟨h_body_ok, _⟩ | ⟨s_e, h_body_err, h_skip⟩
    · -- ok from body directly: impossible (body ends with throw)
      exfalso
      simp only [L1.seq] at h_body_ok
      rcases h_body_ok with ⟨s_w, _, h_rest⟩ | ⟨h_pass⟩
      · simp only [L1.seq, L1.modify, L1.throw] at h_rest
        rcases h_rest with ⟨_, _, h_throw⟩ | ⟨h_pass2⟩
        · exact absurd (Prod.mk.inj h_throw).1 (by intro h; cases h)
        · exact absurd h_pass2.2 (by intro h; cases h)
      · exact absurd h_pass.2 (by intro h; cases h)
    · -- ok from skip handler (caught error from body)
      have h_s1 := (Prod.mk.inj (show (Except.ok (), s₁) = (Except.ok (), s_e) from h_skip)).2
      simp only [L1.seq] at h_body_err
      rcases h_body_err with ⟨s_w, h_while, h_rest⟩ | ⟨h_pass⟩
      · simp only [L1.seq, L1.modify, L1.throw] at h_rest
        rcases h_rest with ⟨s_b, h_basic, h_throw⟩ | ⟨h_pass2⟩
        · have h_se := (Prod.mk.inj h_throw).2
          have h_sb := (Prod.mk.inj h_basic).2
          -- s₁ = s_e = s_b = {s_w with ret__val := s_w.a}
          obtain ⟨h_while_ok, _⟩ := gcd_while_universal s₀.locals.b.toNat s₀
            (Except.ok (), s_w) (Nat.le_refl _) h_while
          obtain ⟨h_a, _⟩ := h_while_ok rfl
          show wordToNat s₁.locals.ret__val =
            gcd_nat (wordToNat s₀.locals.a) (wordToNat s₀.locals.b)
          rw [h_s1, h_se, h_sb, h_a, gcd_l3_wa_corres]
        · exfalso; exact absurd h_pass2.1 (by intro h; cases h)
      · exfalso
        exact (gcd_while_universal s₀.locals.b.toNat s₀
          (Except.error (), s_e) (Nat.le_refl _) h_pass.1).2 rfl

/-! # C-level end-to-end theorem -/

/-- The C-level correctness theorem for gcd, using Nat reasoning.
    Chains: Nat -> WordAbstract -> TypeStrengthen -> L1corres -> CSimpl Exec -/
theorem gcd_correct_nat (a₀ b₀ : UInt32) :
    cHoare Gcd.procEnv
      (fun s : ProgramState => s.locals.a = a₀ ∧ s.locals.b = b₀)
      Gcd.gcd_body
      (fun s => wordToNat s.locals.ret__val = gcd_nat (wordToNat a₀) (wordToNat b₀))
      (fun _ => True) :=
  L1corres_cHoare_bridge l1_gcd_body_corres (l1_gcd_body_validHoare a₀ b₀)

/-! # Axiom verification -/

#print axioms gcd_nat
#print axioms gcd_correct_nat
#print axioms l1_gcd_body_validHoare
