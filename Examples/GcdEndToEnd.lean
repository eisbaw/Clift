-- GcdEndToEnd: Real end-to-end proof from C code to correctness property
--
-- Chain: C source -> CImporter -> Generated/Gcd.lean (CSimpl)
--        -> clift auto-generates Gcd.l1_gcd_body + Gcd.l1_gcd_body_corres
--        -> validHoare on auto-generated L1 body
--        -> cHoare via L1corres_cHoare_bridge
--
-- NO hand-written intermediate L1 body. NO circular L2 spec.
-- The auto-generated Gcd.l1_gcd_body is used throughout.

import Generated.Gcd
import Clift.Lifting.Pipeline
import Clift.Lifting.WordAbstract
import Clift.Tactics


set_option maxHeartbeats 6400000
set_option maxRecDepth 4096

/-! # Stage 1: Run clift to auto-generate L1 body + L1corres proof -/

clift Gcd

-- Verify the auto-generated definitions exist
#check @Gcd.l1_gcd_body        -- : L1Monad Gcd.ProgramState
#check @Gcd.l1_gcd_body_corres -- : L1corres Gcd.procEnv Gcd.l1_gcd_body Gcd.gcd_body

open Gcd

/-! # Stage 2: Pure gcd functions (UInt32 and Nat level)

These define what gcd MEANS mathematically, independently of the C code. -/

/-- Pure Euclidean gcd over UInt32. -/
def gcd_l3' (a b : UInt32) : UInt32 :=
  if h : b = 0 then a
  else
    have : (a % b).toNat < b.toNat := by
      rw [UInt32.toNat_mod]
      exact Nat.mod_lt _ (by
        have : b.toNat ≠ 0 := fun heq => h (UInt32.ext heq)
        omega)
    gcd_l3' b (a % b)
termination_by b.toNat

theorem gcd_l3'_zero (a : UInt32) : gcd_l3' a 0 = a := by
  unfold gcd_l3'; simp

theorem gcd_l3'_rec (a b : UInt32) (hb : b ≠ 0) :
    gcd_l3' a b = gcd_l3' b (a % b) := by
  conv => lhs; unfold gcd_l3'
  simp [hb]

/-- Euclidean gcd over natural numbers. -/
def gcd_nat' (a b : Nat) : Nat :=
  if b = 0 then a
  else gcd_nat' b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero ‹b ≠ 0›)

theorem gcd_nat'_zero (a : Nat) : gcd_nat' a 0 = a := by
  unfold gcd_nat'; simp

theorem gcd_nat'_rec (a b : Nat) (hb : b ≠ 0) :
    gcd_nat' a b = gcd_nat' b (a % b) := by
  conv => lhs; unfold gcd_nat'
  simp [hb]

/-! # Stage 3: WordAbstract correspondence (gcd_l3' <-> gcd_nat') -/

theorem gcd_l3'_wa_corres (a b : UInt32) :
    wordToNat (gcd_l3' a b) = gcd_nat' (wordToNat a) (wordToNat b) := by
  suffices h : ∀ (n : Nat) (a b : UInt32), b.toNat ≤ n →
      wordToNat (gcd_l3' a b) = gcd_nat' (wordToNat a) (wordToNat b) from
    h b.toNat a b (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro a b hle
    have hb0 : b = 0 := by
      have : (0 : UInt32).toNat = 0 := by decide
      exact UInt32.ext (by omega)
    subst hb0
    simp [gcd_l3'_zero, wordToNat_zero, gcd_nat'_zero]
  | succ k ih =>
    intro a b hle
    by_cases hb0 : b = 0
    · subst hb0; simp [gcd_l3'_zero, wordToNat_zero, gcd_nat'_zero]
    · rw [gcd_l3'_rec a b hb0,
          gcd_nat'_rec (wordToNat a) (wordToNat b) (wordToNat_ne_zero hb0)]
      rw [← wordToNat_mod a b]
      apply ih
      have h_dec : (a % b).toNat < b.toNat := by
        rw [UInt32.toNat_mod]
        exact Nat.mod_lt _ (by
          have : b.toNat ≠ 0 := fun heq => hb0 (UInt32.ext heq)
          omega)
      omega

/-! # Stage 4: L1 while body analysis on the AUTO-GENERATED body

The auto-generated Gcd.l1_gcd_body has the structure:
  L1.catch
    (L1.seq
      (L1.while cond body)
      (L1.seq (L1.modify ret:=a) L1.throw))
    L1.skip

We extract the while body and prove properties about it. -/

/-- The while body extracted from the auto-generated L1 body. -/
abbrev gcd_while_body' : L1Monad ProgramState :=
  L1.seq
    (L1.modify (fun s => { s with locals := { s.locals with t := s.locals.b } }))
    (L1.seq
      (L1.seq (L1.guard (fun s => s.locals.b ≠ 0))
        (L1.modify (fun s => { s with locals := { s.locals with b := (s.locals.a % s.locals.b) } })))
      (L1.modify (fun s => { s with locals := { s.locals with a := s.locals.t } })))

/-- The while body only produces ok results with known values. -/
private theorem gcd_body_only_ok' (s : ProgramState)
    (hb : s.locals.b ≠ 0)
    (e : Except Unit Unit) (t : ProgramState)
    (h : (e, t) ∈ (gcd_while_body' s).results) :
    e = Except.ok () ∧
    t.locals.a = s.locals.b ∧ t.locals.b = s.locals.a % s.locals.b ∧ t.globals = s.globals := by
  unfold gcd_while_body' L1.seq L1.modify L1.guard at h
  rcases h with ⟨s1, h_m1, h_rest⟩ | ⟨h_err, _⟩
  · have h_e1 := (Prod.mk.inj h_m1).1
    have h_s1 := (Prod.mk.inj h_m1).2
    rcases h_rest with ⟨s2, h_inner, h_m3⟩ | ⟨h_err2, _⟩
    · rcases h_inner with ⟨s_g, h_guard, h_m2⟩ | ⟨h_err3, _⟩
      · subst h_s1
        simp [hb] at h_guard
        subst h_guard
        have h_e2 := (Prod.mk.inj h_m2).1
        have h_s2 := (Prod.mk.inj h_m2).2
        have h_e3 := (Prod.mk.inj h_m3).1
        have h_t := (Prod.mk.inj h_m3).2
        subst h_e3 h_t h_s2
        exact ⟨rfl, rfl, rfl, rfl⟩
      · subst h_s1
        simp [hb] at h_err3
    · subst h_s1
      rcases h_err2 with ⟨s_g, h_guard, h_m2⟩ | ⟨h_err3, _⟩
      · simp [hb] at h_guard
        subst h_guard
        exact absurd (Prod.mk.inj h_m2).1 (by intro h; cases h)
      · simp [hb] at h_err3
  · exact absurd (Prod.mk.inj h_err).1 (by intro h; cases h)

/-- The while body never fails when guard holds. -/
theorem gcd_while_body'_not_failed (s : ProgramState) (hb : s.locals.b ≠ 0) :
    ¬(gcd_while_body' s).failed := by
  unfold gcd_while_body' L1.seq L1.modify L1.guard
  simp [hb]

/-! # Stage 5: While loop computes gcd_l3' -/

/-- For ALL WhileResult outcomes: ok-outcomes compute gcd_l3', error-outcomes impossible. -/
private theorem gcd_while_universal' (n : Nat) :
    ∀ (s : ProgramState) (p : Except Unit Unit × ProgramState),
    s.locals.b.toNat ≤ n →
    L1.WhileResult (fun s => decide (s.locals.b ≠ 0)) gcd_while_body' s p →
    (p.1 = Except.ok () →
      p.2.locals.a = gcd_l3' s.locals.a s.locals.b ∧ p.2.globals = s.globals) ∧
    (p.1 = Except.error () → False) := by
  induction n with
  | zero =>
    intro s p hle h_w
    have hb0 : s.locals.b = 0 := by
      have : (0 : UInt32).toNat = 0 := by decide
      exact UInt32.ext (by omega)
    cases h_w with
    | done s0 hc =>
      exact ⟨fun _ => ⟨by rw [hb0, gcd_l3'_zero], rfl⟩, fun h => by cases h⟩
    | step s0 t q hc => simp [hb0] at hc
    | abrupt s0 t hc => simp [hb0] at hc
  | succ k ih =>
    intro s p hle h_w
    cases h_w with
    | done _ hc =>
      have hb0 : s.locals.b = 0 := by
        simp at hc; exact hc
      exact ⟨fun _ => ⟨by rw [hb0, gcd_l3'_zero], rfl⟩, fun h => by cases h⟩
    | step _ t _ hc h_body h_rest =>
      have hb_ne : s.locals.b ≠ 0 := by
        simp at hc; exact hc
      obtain ⟨_, h_ta, h_tb, h_tg⟩ := gcd_body_only_ok' s hb_ne _ t h_body
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
        exact ⟨by rw [ih_a, h_ta, h_tb, ← gcd_l3'_rec _ _ hb_ne], by rw [ih_g, h_tg]⟩,
        ih_err⟩
    | abrupt _ t hc h_body =>
      exfalso
      have hb_ne' : s.locals.b ≠ 0 := by simp at hc; exact hc
      obtain ⟨h_ok, _, _, _⟩ := gcd_body_only_ok' s hb_ne' _ t h_body
      exact absurd h_ok (by intro h; cases h)

/-! # Stage 6: The auto-generated L1 body never fails -/

theorem auto_l1_gcd_body_not_failed (s : ProgramState) :
    ¬(Gcd.l1_gcd_body s).failed := by
  unfold Gcd.l1_gcd_body
  simp only [L1.catch]
  intro h
  rcases h with h_body | ⟨s', h_err, h_skip_fail⟩
  · simp only [L1.seq] at h_body
    rcases h_body with h_while_fail | ⟨s', h_while_ok, h_rest_fail⟩
    · induction h_while_fail with
      | here s hc h_fail =>
        have hb : s.locals.b ≠ 0 := by simpa using hc
        exact gcd_while_body'_not_failed s hb h_fail
      | later s t hc h_body h_rest ih => exact ih
    · simp only [L1.modify, L1.throw] at h_rest_fail
      rcases h_rest_fail with h_fail | ⟨_, _, h_fail⟩
      · exact h_fail
      · exact h_fail
  · exact h_skip_fail

/-! # Stage 7: validHoare on the AUTO-GENERATED Gcd.l1_gcd_body -/

theorem auto_l1_gcd_body_validHoare (a₀ b₀ : UInt32) :
    validHoare
      (fun s : ProgramState => s.locals.a = a₀ ∧ s.locals.b = b₀)
      Gcd.l1_gcd_body
      (fun r s =>
        match r with
        | Except.ok () =>
          wordToNat s.locals.ret__val = gcd_nat' (wordToNat a₀) (wordToNat b₀)
        | Except.error () => True) := by
  intro s₀ ⟨ha, hb⟩; subst ha; subst hb
  refine ⟨auto_l1_gcd_body_not_failed s₀, ?_⟩
  intro r s₁ h_mem
  match r with
  | Except.error () => trivial
  | Except.ok () =>
    unfold Gcd.l1_gcd_body at h_mem
    simp only [L1.catch] at h_mem
    rcases h_mem with ⟨h_body_ok, _⟩ | ⟨s_e, h_body_err, h_skip⟩
    · -- ok from body directly: impossible (body ends with throw)
      exfalso
      simp only [L1.seq] at h_body_ok
      rcases h_body_ok with ⟨s_w, _, h_rest⟩ | ⟨h_pass⟩
      · simp only [L1.modify, L1.throw] at h_rest
        rcases h_rest with ⟨_, _, h_throw⟩ | ⟨h_pass2⟩
        · exact absurd (Prod.mk.inj h_throw).1 (by intro h; cases h)
        · exact absurd h_pass2.2 (by intro h; cases h)
      · exact absurd h_pass.2 (by intro h; cases h)
    · -- ok from skip handler (caught error from body)
      have h_s1 := (Prod.mk.inj (show (Except.ok (), s₁) = (Except.ok (), s_e) from h_skip)).2
      simp only [L1.seq] at h_body_err
      rcases h_body_err with ⟨s_w, h_while, h_rest⟩ | ⟨h_pass⟩
      · simp only [L1.modify, L1.throw] at h_rest
        rcases h_rest with ⟨s_b, h_basic, h_throw⟩ | ⟨h_pass2⟩
        · have h_se := (Prod.mk.inj h_throw).2
          have h_sb := (Prod.mk.inj h_basic).2
          obtain ⟨h_while_ok, _⟩ := gcd_while_universal' s₀.locals.b.toNat s₀
            (Except.ok (), s_w) (Nat.le_refl _) h_while
          obtain ⟨h_a, _⟩ := h_while_ok rfl
          show wordToNat s₁.locals.ret__val =
            gcd_nat' (wordToNat s₀.locals.a) (wordToNat s₀.locals.b)
          rw [h_s1, h_se, h_sb, h_a, gcd_l3'_wa_corres]
        · exfalso; exact absurd h_pass2.1 (by intro h; cases h)
      · exfalso
        exact (gcd_while_universal' s₀.locals.b.toNat s₀
          (Except.error (), s_e) (Nat.le_refl _) h_pass.1).2 rfl

/-! # Stage 8: The end-to-end theorem

C gcd() computes GCD over natural numbers.

Chain: Generated/Gcd.lean (CImporter from C)
       -> clift auto-generates Gcd.l1_gcd_body + Gcd.l1_gcd_body_corres
       -> validHoare proved above
       -> cHoare via L1corres_cHoare_bridge -/

theorem gcd_correct_nat_e2e (a₀ b₀ : UInt32) :
    cHoare Gcd.procEnv
      (fun s : ProgramState => s.locals.a = a₀ ∧ s.locals.b = b₀)
      Gcd.gcd_body
      (fun s => wordToNat s.locals.ret__val = gcd_nat' (wordToNat a₀) (wordToNat b₀))
      (fun _ => True) :=
  L1corres_cHoare_bridge Gcd.l1_gcd_body_corres (auto_l1_gcd_body_validHoare a₀ b₀)

/-! # Stage 9: Axiom verification -/

#print axioms gcd_correct_nat_e2e
#print axioms auto_l1_gcd_body_validHoare
#print axioms Gcd.l1_gcd_body_corres
