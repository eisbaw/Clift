-- UInt64 extensionality lemma.
--
-- Two UInt64 values are equal iff their toNat values are equal.

/-- If two UInt64 values have the same toNat, they are equal. -/
theorem UInt64.ext {a b : UInt64} (h : a.toNat = b.toNat) : a = b :=
  congrArg (⟨·⟩ : BitVec 64 → UInt64) (BitVec.eq_of_toNat_eq h)
