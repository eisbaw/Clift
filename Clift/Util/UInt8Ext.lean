-- UInt8 extensionality lemma.
--
-- Two UInt8 values are equal iff their toNat values are equal.

/-- If two UInt8 values have the same toNat, they are equal. -/
theorem UInt8.ext {a b : UInt8} (h : a.toNat = b.toNat) : a = b :=
  congrArg (⟨·⟩ : BitVec 8 → UInt8) (BitVec.eq_of_toNat_eq h)
