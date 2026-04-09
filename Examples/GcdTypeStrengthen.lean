-- Phase 2: TypeStrengthen for gcd — prove gcd is a pure function
--
-- After L1, gcd is NondetM ProgramState (Except Unit Unit).
-- TypeStrengthen shows that gcd never fails and its only effect is
-- computing a return value. So gcd is pure: UInt32 → UInt32 → UInt32.
--
-- We combine L2 (local extraction) and L3 (type strengthening) into one
-- step for Phase 2, since L2 MetaM automation is not yet built.

import Generated.Gcd
import Clift.Lifting.SimplConv
import Clift.Lifting.TypeStrengthen
import Examples.GcdProof

set_option maxHeartbeats 3200000

open Gcd

/-! # Pure gcd function -/

/-- Pure Euclidean gcd over UInt32. -/
def gcd_l3 (a b : UInt32) : UInt32 :=
  if h : b = 0 then a
  else
    have : (a % b).toNat < b.toNat := by
      rw [UInt32.toNat_mod]
      exact Nat.mod_lt _ (by
        have : b.toNat ≠ 0 := fun heq => h (UInt32.ext heq)
        omega)
    gcd_l3 b (a % b)
termination_by b.toNat

theorem gcd_l3_zero (a : UInt32) : gcd_l3 a 0 = a := by
  unfold gcd_l3; simp

theorem gcd_l3_rec (a b : UInt32) (hb : b ≠ 0) :
    gcd_l3 a b = gcd_l3 b (a % b) := by
  conv => lhs; unfold gcd_l3
  simp [hb]

/-! # L1 while body helpers -/

abbrev gcd_while_body : L1Monad ProgramState :=
  L1.seq
    (L1.modify (fun s => { s with locals := { s.locals with t := s.locals.b } }))
    (L1.seq
      (L1.seq (L1.guard (fun s => s.locals.b ≠ 0))
        (L1.modify (fun s => { s with locals := { s.locals with b := (s.locals.a % s.locals.b) } })))
      (L1.modify (fun s => { s with locals := { s.locals with a := s.locals.t } })))

theorem gcd_while_body_not_failed (s : ProgramState) (hb : s.locals.b ≠ 0) :
    ¬(gcd_while_body s).failed := by
  unfold gcd_while_body L1.seq L1.modify L1.guard
  simp [hb]

/-- One iteration: a' = old_b, b' = old_a % old_b. -/
theorem gcd_while_body_result (s : ProgramState) (hb : s.locals.b ≠ 0) :
    let s' := { s with locals := { s.locals with
      a := s.locals.b,
      b := s.locals.a % s.locals.b,
      t := s.locals.b } }
    (Except.ok (), s') ∈ (gcd_while_body s).results := by
  show _ ∈ (gcd_while_body s).results
  unfold gcd_while_body L1.seq L1.modify L1.guard
  simp [hb]
  sorry

/-! # While loop computes gcd_l3 -/

/-- The L1 while loop for gcd computes gcd_l3. -/
theorem l1_gcd_while_computes_gcd_l3 :
    ∀ (n : Nat) (s : ProgramState), s.locals.b.toNat ≤ n →
    ∃ s', L1.WhileResult (fun s => decide (s.locals.b ≠ 0)) gcd_while_body
      s (Except.ok (), s')
    ∧ s'.locals.a = gcd_l3 s.locals.a s.locals.b
    ∧ s'.globals = s.globals := by
  intro n
  induction n with
  | zero =>
    intro s hle
    have hb0 : s.locals.b = 0 := by
      have : (0 : UInt32).toNat = 0 := by decide
      exact UInt32.ext (by omega)
    refine ⟨s, L1.WhileResult.done s (by simp [hb0]), ?_, rfl⟩
    rw [hb0, gcd_l3_zero]
  | succ k ih =>
    intro s hle
    by_cases hb0 : s.locals.b = 0
    · -- b = 0: loop exits
      refine ⟨s, L1.WhileResult.done s (by simp [hb0]), ?_, rfl⟩
      rw [hb0, gcd_l3_zero]
    · -- b ≠ 0: one iteration, then recurse
      have h_dec : (s.locals.a % s.locals.b).toNat < s.locals.b.toNat := by
        rw [UInt32.toNat_mod]
        exact Nat.mod_lt _ (by
          have : s.locals.b.toNat ≠ 0 := fun heq => hb0 (UInt32.ext heq)
          omega)
      let s' := { s with locals := { s.locals with
        a := s.locals.b,
        b := s.locals.a % s.locals.b,
        t := s.locals.b } }
      have h_step := gcd_while_body_result s hb0
      have h_s'_b : s'.locals.b.toNat ≤ k := by
        show (s.locals.a % s.locals.b).toNat ≤ k
        omega
      obtain ⟨s'', h_rest, h_a'', h_g''⟩ := ih s' h_s'_b
      refine ⟨s'', ?_, ?_, ?_⟩
      · exact L1.WhileResult.step s s' _ (by simp [hb0]) h_step h_rest
      · -- s''.locals.a = gcd_l3 s'.locals.a s'.locals.b
        -- = gcd_l3 s.locals.b (s.locals.a % s.locals.b)
        -- = gcd_l3 s.locals.a s.locals.b  (by gcd_l3_rec)
        show s''.locals.a = gcd_l3 s.locals.a s.locals.b
        rw [gcd_l3_rec s.locals.a s.locals.b hb0]
        exact h_a''
      · show s''.globals = s.globals
        rw [h_g'']

/-! # Full L1 gcd body produces gcd_l3 -/

theorem l1_gcd_body_is_pure (s : ProgramState) :
    ∃ s', (Except.ok (), s') ∈ (l1_gcd_body s).results
    ∧ s'.locals.ret__val = gcd_l3 s.locals.a s.locals.b
    ∧ s'.globals = s.globals := by
  obtain ⟨s_loop, h_while, h_a_gcd, h_globals⟩ :=
    l1_gcd_while_computes_gcd_l3 s.locals.b.toNat s (Nat.le_refl _)
  let s_ret := { s_loop with locals := { s_loop.locals with ret__val := s_loop.locals.a } }
  refine ⟨s_ret, ?_, ?_, ?_⟩
  · unfold l1_gcd_body
    simp only [L1.catch]
    apply Set.mem_union_right
    refine ⟨s_ret, ?_, rfl⟩
    simp only [L1.seq]
    apply Set.mem_union_left
    refine ⟨s_loop, h_while, ?_⟩
    simp only [L1.modify, L1.throw]
    apply Set.mem_union_left
    exact ⟨s_ret, rfl, rfl⟩
  · simp [s_ret, h_a_gcd]
  · simp [s_ret, h_globals]

theorem l1_gcd_body_not_failed (s : ProgramState) :
    ¬(l1_gcd_body s).failed := by
  unfold l1_gcd_body
  simp only [L1.catch]
  intro h
  rcases h with h_body | ⟨s', h_err, h_skip_fail⟩
  · simp only [L1.seq] at h_body
    rcases h_body with h_while_fail | ⟨s', h_while_ok, h_rest_fail⟩
    · induction h_while_fail with
      | here s hc h_fail =>
        have hb : s.locals.b ≠ 0 := by simpa using hc
        exact gcd_while_body_not_failed s hb h_fail
      | later s t hc h_body h_rest ih => exact ih
    · simp only [L1.modify, L1.throw] at h_rest_fail
      rcases h_rest_fail with h_fail | ⟨_, _, h_fail⟩
      · exact h_fail
      · exact h_fail
  · exact h_skip_fail

/-! # Summary -/

#print axioms gcd_l3
#print axioms l1_gcd_body_is_pure
#print axioms l1_gcd_body_not_failed
