-- Phase 2: WordAbstract for gcd — lift UInt32 to Nat
--
-- After TypeStrengthen: gcd_l3 : UInt32 → UInt32 → UInt32
-- After WordAbstract: gcd_nat : Nat → Nat → Nat
--
-- The correspondence: for all a b : UInt32,
--   wordToNat (gcd_l3 a b) = gcd_nat (wordToNat a) (wordToNat b)
--
-- For gcd, this holds unconditionally because:
-- 1. % on UInt32 matches % on Nat (UInt32.toNat_mod)
-- 2. The gcd result is always ≤ max(a, b), so stays in UInt32 range
-- 3. No addition/multiplication that could overflow

import Clift.Lifting.WordAbstract
import Examples.GcdTypeStrengthen

set_option maxHeartbeats 3200000

/-! # Nat-level gcd function -/

/-- Euclidean gcd over natural numbers. This is the final "clean" version
    that users reason about. -/
def gcd_nat (a b : Nat) : Nat :=
  if b = 0 then a
  else gcd_nat b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero ‹b ≠ 0›)

theorem gcd_nat_zero (a : Nat) : gcd_nat a 0 = a := by
  unfold gcd_nat; simp

theorem gcd_nat_rec (a b : Nat) (hb : b ≠ 0) :
    gcd_nat a b = gcd_nat b (a % b) := by
  conv => lhs; unfold gcd_nat
  simp [hb]

/-! # WAcorres: gcd_l3 corresponds to gcd_nat

The key theorem: wordToNat (gcd_l3 a b) = gcd_nat (wordToNat a) (wordToNat b)

Proof by well-founded induction on b.toNat, using:
- wordToNat_mod: (a % b).toNat = a.toNat % b.toNat
- gcd_l3_rec and gcd_nat_rec unfold in lockstep
-/

theorem gcd_l3_wa_corres (a b : UInt32) :
    wordToNat (gcd_l3 a b) = gcd_nat (wordToNat a) (wordToNat b) := by
  -- Strong induction on b.toNat
  suffices h : ∀ (n : Nat) (a b : UInt32), b.toNat ≤ n →
      wordToNat (gcd_l3 a b) = gcd_nat (wordToNat a) (wordToNat b) from
    h b.toNat a b (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro a b hle
    have hb0 : b = 0 := by
      have : (0 : UInt32).toNat = 0 := by decide
      exact UInt32.ext (by omega)
    subst hb0
    simp [gcd_l3_zero, wordToNat_zero, gcd_nat_zero]
  | succ k ih =>
    intro a b hle
    by_cases hb0 : b = 0
    · subst hb0; simp [gcd_l3_zero, wordToNat_zero, gcd_nat_zero]
    · rw [gcd_l3_rec a b hb0,
          gcd_nat_rec (wordToNat a) (wordToNat b) (wordToNat_ne_zero hb0)]
      rw [← wordToNat_mod a b]
      apply ih
      have h_dec : (a % b).toNat < b.toNat := by
        rw [UInt32.toNat_mod]
        exact Nat.mod_lt _ (by
          have : b.toNat ≠ 0 := fun heq => hb0 (UInt32.ext heq)
          omega)
      omega

/-! # End-to-end: gcd_nat is the final abstraction of gcd_l3.
    WAcorres_pure2 holds for gcd with trivial (always true) guard. -/

theorem gcd_WAcorres :
    WAcorres_pure2 gcd_l3 gcd_nat (fun _ _ => True) := by
  intro a b _
  exact gcd_l3_wa_corres a b

#print axioms gcd_nat
#print axioms gcd_l3_wa_corres
#print axioms gcd_WAcorres
