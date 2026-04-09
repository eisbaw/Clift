-- L5: WordAbstract — UInt32 to Nat with range guards
--
-- Reference: ext/AutoCorres2/WordAbstract.thy, ext/AutoCorres2/word_abstract.ML
--
-- Unsigned word abstraction: UInt32 → Nat with guard n < 2^32
-- Signed word abstraction: deferred (not needed for gcd)
--
-- Key insight: if all intermediate values stay in range, then
-- UInt32 arithmetic (wrapping modulo 2^32) matches Nat arithmetic.
-- For modular operations like %, the correspondence holds unconditionally.
--
-- For Phase 2: manual/definitional approach. MetaM automation deferred.

import Clift.MonadLib
import Clift.Util.UInt32Ext

set_option maxHeartbeats 800000

/-! # Abstraction function: UInt32 <-> Nat -/

/-- Convert UInt32 to Nat. This is the word abstraction function. -/
def wordToNat (w : UInt32) : Nat := w.toNat

/-- Convert Nat to UInt32. Requires the Nat is in range [0, 2^32). -/
def natToWord (n : Nat) (h : n < 2 ^ 32) : UInt32 := ⟨⟨n, h⟩⟩

/-! # Roundtrip lemmas -/

/-- Roundtrip: wordToNat (natToWord n) = n -/
theorem wordToNat_natToWord (n : Nat) (h : n < 2 ^ 32) :
    wordToNat (natToWord n h) = n := rfl

/-- Roundtrip: natToWord (wordToNat w) = w -/
theorem natToWord_wordToNat (w : UInt32) :
    natToWord (wordToNat w) (w.toBitVec.isLt) = w := by
  cases w; rfl

/-- wordToNat always produces a value in range. -/
theorem wordToNat_inRange (w : UInt32) : wordToNat w < 2 ^ 32 :=
  w.toBitVec.isLt

/-! # Arithmetic correspondence lemmas -/

/-- UInt32 zero maps to Nat zero. -/
theorem wordToNat_zero : wordToNat (0 : UInt32) = 0 := by decide

/-- UInt32 modulo corresponds to Nat modulo (unconditionally). -/
theorem wordToNat_mod (a b : UInt32) :
    wordToNat (a % b) = wordToNat a % wordToNat b :=
  UInt32.toNat_mod a b

/-- UInt32 equality ↔ Nat equality. -/
theorem wordToNat_eq_iff (a b : UInt32) :
    wordToNat a = wordToNat b ↔ a = b :=
  ⟨fun h => UInt32.ext h, fun h => congrArg wordToNat h⟩

/-- UInt32 nonzero ↔ Nat nonzero. -/
theorem wordToNat_ne_zero {b : UInt32} (hb : b ≠ 0) :
    wordToNat b ≠ 0 := by
  intro h
  apply hb
  have : b.toNat = 0 := h
  exact UInt32.ext this

/-- UInt32 addition corresponds to Nat addition when result is in range.
    UInt32 addition wraps modulo 2^32, so we need the sum to be in range. -/
theorem wordToNat_add (a b : UInt32)
    (h : wordToNat a + wordToNat b < 2 ^ 32) :
    wordToNat (a + b) = wordToNat a + wordToNat b := by
  have := UInt32.toNat_add a b
  -- this : (a + b).toNat = (a.toNat + b.toNat) % 2 ^ 32
  -- Since sum < 2^32, the mod is a no-op
  simp only [wordToNat] at *
  omega

/-! # WAcorres: word abstraction correspondence

WAcorres connects a word-level function to a Nat-level function
under range guards. For Phase 2, this is a simple relation stating
that the abstraction commutes with the function.
-/

/-- WAcorres for binary pure functions: f_word and f_nat agree
    under wordToNat, given a range guard on the inputs. -/
def WAcorres_pure2
    (f_word : UInt32 → UInt32 → UInt32)
    (f_nat : Nat → Nat → Nat)
    (guard : Nat → Nat → Prop) : Prop :=
  ∀ a b : UInt32,
    guard (wordToNat a) (wordToNat b) →
    wordToNat (f_word a b) = f_nat (wordToNat a) (wordToNat b)
