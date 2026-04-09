-- UInt32 extensionality lemma.
--
-- Replaces Mathlib's UInt32.ext which was the only thing we used
-- from Mathlib.Data.Fin.Basic (transitively).
--
-- In Lean 4.30, UInt32 wraps BitVec 32.
-- Two UInt32 values are equal iff their toNat values are equal.

/-- If two UInt32 values have the same toNat, they are equal.
    This replaces Mathlib.Data.Fin.Basic's UInt32.ext. -/
theorem UInt32.ext {a b : UInt32} (h : a.toNat = b.toNat) : a = b :=
  congrArg (⟨·⟩ : BitVec 32 → UInt32) (BitVec.eq_of_toNat_eq h)
