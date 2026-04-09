-- UInt16 extensionality lemma.
--
-- Two UInt16 values are equal iff their toNat values are equal.

/-- If two UInt16 values have the same toNat, they are equal. -/
theorem UInt16.ext {a b : UInt16} (h : a.toNat = b.toNat) : a = b :=
  congrArg (⟨·⟩ : BitVec 16 → UInt16) (BitVec.eq_of_toNat_eq h)
