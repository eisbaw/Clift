-- State types: HeapRawState, Ptr, typed heap access
--
-- Phase 0-3a: memory model with typed read/write.
-- Extended in Phase 3c with HeapLift (typed split heaps).
--
-- Reference: plan.md Decision 8
-- Reference: ext/AutoCorres2/c-parser/umm_heap/HeapRawState.thy
-- Reference: ext/AutoCorres2/TypHeapSimple.thy

import Clift.CSemantics.TypeTag
import Clift.Util.UInt8Ext
import Clift.Util.UInt16Ext
import Clift.Util.UInt32Ext
import Clift.Util.UInt64Ext

set_option maxHeartbeats 800000

/-! # Memory model constants -/

/-- Memory size in bytes. Using 2^32 for a 32-bit address space. -/
def memSize : Nat := 2^32

/-! # Raw heap state -/

/-- Byte-level heap with type tracking.
    - `mem`: byte-addressed memory
    - `htd`: heap type descriptor — what type is stored at each address -/
structure HeapRawState where
  mem : Fin memSize → UInt8
  htd : Fin memSize → Option TypeTag

/-! # Typed pointer -/

/-- Pointer with phantom type tag. -/
structure Ptr (α : Type) where
  addr : Fin memSize
  deriving Repr

/-- DecidableEq for Ptr that does NOT require DecidableEq α.
    Ptr equality depends only on the address, not the phantom type parameter. -/
instance {α : Type} : DecidableEq (Ptr α) := fun p q =>
  if h : p.addr = q.addr then
    isTrue (by cases p; cases q; simp at h; exact congrArg _ h)
  else
    isFalse (by intro heq; apply h; cases heq; rfl)

instance {α : Type} : Inhabited (Ptr α) := ⟨⟨⟨0, by unfold memSize; omega⟩⟩⟩

/-- Null pointer constant. Address 0 is never valid. -/
def Ptr.null {α : Type} : Ptr α := ⟨⟨0, by unfold memSize; omega⟩⟩

/-! # CType typeclass -/

/-- Typeclass for C types that can be stored in the heap. -/
class CType (α : Type) where
  /-- Size in bytes. Must be > 0. -/
  size : Nat
  /-- Alignment requirement in bytes -/
  align : Nat
  /-- TypeTag for heap type descriptor tracking -/
  typeTag : TypeTag
  /-- Size is positive -/
  size_pos : 0 < size

/-! # MemType typeclass: typed heap access

For Phase 3a, we model typed memory access abstractly: each MemType
provides fromMem/toMem to read/write a value using CType.size
bytes of Fin-indexed memory. This keeps everything computable. -/
class MemType (α : Type) extends CType α where
  /-- Read a value from `size` consecutive bytes. -/
  fromMem : (Fin size → UInt8) → α
  /-- Write a value to `size` consecutive bytes. -/
  toMem : α → (Fin size → UInt8)
  /-- Roundtrip: fromMem (toMem v) = v. -/
  roundtrip : ∀ (v : α), fromMem (toMem v) = v

/-! # UInt32 MemType instance

For Phase 3a, we store UInt32 as 4 bytes (little-endian).
The encoding uses Nat division and modulus with concrete constants
to keep proofs simple. -/

/-- Reassemble a UInt32 from 4 bytes using Nat arithmetic. -/
private def assembleByte (b0 b1 b2 b3 : UInt8) : UInt32 :=
  ⟨⟨b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216, by
    have h0 := b0.toBitVec.isLt
    have h1 := b1.toBitVec.isLt
    have h2 := b2.toBitVec.isLt
    have h3 := b3.toBitVec.isLt
    simp only [UInt8.toNat] at *
    omega⟩⟩

/-- Read UInt32 from 4 bytes (little-endian). -/
def UInt32.fromBytes' (f : Fin 4 → UInt8) : UInt32 :=
  assembleByte (f ⟨0, by omega⟩) (f ⟨1, by omega⟩) (f ⟨2, by omega⟩) (f ⟨3, by omega⟩)

/-- Write UInt32 to 4 bytes (little-endian) using concrete divisors. -/
def UInt32.toBytes' (v : UInt32) : Fin 4 → UInt8 := fun i =>
  match i with
  | ⟨0, _⟩ => ⟨⟨v.toNat % 256, by omega⟩⟩
  | ⟨1, _⟩ => ⟨⟨v.toNat / 256 % 256, by omega⟩⟩
  | ⟨2, _⟩ => ⟨⟨v.toNat / 65536 % 256, by omega⟩⟩
  | ⟨3, _⟩ => ⟨⟨v.toNat / 16777216 % 256, by omega⟩⟩

/-- Byte decomposition identity: any n < 2^32 equals the sum of its 4 bytes. -/
private theorem byte_decompose (n : Nat) (hn : n < 4294967296) :
    n % 256 + n / 256 % 256 * 256 + n / 65536 % 256 * 65536
    + n / 16777216 % 256 * 16777216 = n := by
  have h1 : n % 256 + 256 * (n / 256) = n := Nat.mod_add_div n 256
  have h2 : n / 256 % 256 + 256 * (n / 256 / 256) = n / 256 :=
    Nat.mod_add_div (n / 256) 256
  have h3 : n / 256 / 256 % 256 + 256 * (n / 256 / 256 / 256) = n / 256 / 256 :=
    Nat.mod_add_div (n / 256 / 256) 256
  have h4 : n / 256 / 256 / 256 < 256 := by omega
  have h5 : n / 256 / 256 / 256 % 256 = n / 256 / 256 / 256 :=
    Nat.mod_eq_of_lt h4
  have h6 : n / 256 / 256 = n / 65536 := by omega
  have h7 : n / 256 / 256 / 256 = n / 16777216 := by omega
  omega

/-- UInt32 roundtrip: fromBytes' (toBytes' v) = v.
    Strategy: show the assembled value has the same toNat as v,
    then use UInt32.ext to conclude equality. -/
theorem UInt32.fromBytes_toBytes' (v : UInt32) :
    UInt32.fromBytes' (UInt32.toBytes' v) = v := by
  -- Step 1: Show the assembled UInt32 has the correct toNat value
  have hv : v.toNat < 4294967296 := v.toBitVec.isLt
  have hd := byte_decompose v.toNat hv
  -- Step 2: The fromBytes' (toBytes' v) unfolds to assembleByte of the 4 extracted bytes
  show UInt32.fromBytes' (UInt32.toBytes' v) = v
  -- We prove this by showing .toNat values match
  suffices h : (UInt32.fromBytes' (UInt32.toBytes' v)).toNat = v.toNat from
    UInt32.ext h
  -- Unfold definitions
  show (assembleByte
    (⟨⟨v.toNat % 256, by omega⟩⟩ : UInt8)
    (⟨⟨v.toNat / 256 % 256, by omega⟩⟩ : UInt8)
    (⟨⟨v.toNat / 65536 % 256, by omega⟩⟩ : UInt8)
    (⟨⟨v.toNat / 16777216 % 256, by omega⟩⟩ : UInt8)).toNat = v.toNat
  -- assembleByte produces a UInt32 with toNat = sum of byte values
  -- Reduce: (⟨⟨n, h⟩⟩ : UInt32).toNat = n for any n < 2^32
  -- This is definitional: UInt32.toNat (UInt32.ofBitVec ⟨n, h⟩) = n
  show v.toNat % 256 + v.toNat / 256 % 256 * 256
        + v.toNat / 65536 % 256 * 65536
        + v.toNat / 16777216 % 256 * 16777216 = v.toNat
  exact hd

instance : MemType UInt32 where
  size := 4
  align := 4
  typeTag := ⟨1⟩
  size_pos := by omega
  fromMem := UInt32.fromBytes'
  toMem := UInt32.toBytes'
  roundtrip := UInt32.fromBytes_toBytes'

/-! # UInt8 MemType instance -/

/-- Read UInt8 from 1 byte. -/
def UInt8.fromBytes' (f : Fin 1 → UInt8) : UInt8 := f ⟨0, by omega⟩

/-- Write UInt8 to 1 byte. -/
def UInt8.toBytes' (v : UInt8) : Fin 1 → UInt8 := fun _ => v

theorem UInt8.fromBytes_toBytes' (v : UInt8) :
    UInt8.fromBytes' (UInt8.toBytes' v) = v := by
  simp [UInt8.fromBytes', UInt8.toBytes']

instance : MemType UInt8 where
  size := 1
  align := 1
  typeTag := ⟨2⟩
  size_pos := by omega
  fromMem := UInt8.fromBytes'
  toMem := UInt8.toBytes'
  roundtrip := UInt8.fromBytes_toBytes'

/-! # UInt16 MemType instance (little-endian, 2 bytes) -/

/-- Reassemble a UInt16 from 2 bytes. -/
private def assembleByte16 (b0 b1 : UInt8) : UInt16 :=
  ⟨⟨b0.toNat + b1.toNat * 256, by
    have h0 := b0.toBitVec.isLt
    have h1 := b1.toBitVec.isLt
    simp only [UInt8.toNat] at *
    omega⟩⟩

/-- Read UInt16 from 2 bytes (little-endian). -/
def UInt16.fromBytes' (f : Fin 2 → UInt8) : UInt16 :=
  assembleByte16 (f ⟨0, by omega⟩) (f ⟨1, by omega⟩)

/-- Write UInt16 to 2 bytes (little-endian). -/
def UInt16.toBytes' (v : UInt16) : Fin 2 → UInt8 := fun i =>
  match i with
  | ⟨0, _⟩ => ⟨⟨v.toNat % 256, by omega⟩⟩
  | ⟨1, _⟩ => ⟨⟨v.toNat / 256 % 256, by omega⟩⟩

/-- Byte decomposition for UInt16: n < 2^16 => n%256 + (n/256)%256*256 = n. -/
private theorem byte_decompose16 (n : Nat) (hn : n < 65536) :
    n % 256 + n / 256 % 256 * 256 = n := by
  have h1 : n % 256 + 256 * (n / 256) = n := Nat.mod_add_div n 256
  have h2 : n / 256 < 256 := by omega
  have h3 : n / 256 % 256 = n / 256 := Nat.mod_eq_of_lt h2
  omega

theorem UInt16.fromBytes_toBytes' (v : UInt16) :
    UInt16.fromBytes' (UInt16.toBytes' v) = v := by
  have hv : v.toNat < 65536 := v.toBitVec.isLt
  suffices h : (UInt16.fromBytes' (UInt16.toBytes' v)).toNat = v.toNat from
    UInt16.ext h
  show v.toNat % 256 + v.toNat / 256 % 256 * 256 = v.toNat
  exact byte_decompose16 v.toNat hv

instance : MemType UInt16 where
  size := 2
  align := 2
  typeTag := ⟨3⟩
  size_pos := by omega
  fromMem := UInt16.fromBytes'
  toMem := UInt16.toBytes'
  roundtrip := UInt16.fromBytes_toBytes'

/-! # UInt64 MemType instance (little-endian, 8 bytes) -/

/-- Reassemble a UInt64 from 8 bytes using Nat arithmetic. -/
private def assembleByte64 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : UInt64 :=
  ⟨⟨b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216
   + b4.toNat * 4294967296 + b5.toNat * 1099511627776
   + b6.toNat * 281474976710656 + b7.toNat * 72057594037927936, by
    have h0 := b0.toBitVec.isLt
    have h1 := b1.toBitVec.isLt
    have h2 := b2.toBitVec.isLt
    have h3 := b3.toBitVec.isLt
    have h4 := b4.toBitVec.isLt
    have h5 := b5.toBitVec.isLt
    have h6 := b6.toBitVec.isLt
    have h7 := b7.toBitVec.isLt
    simp only [UInt8.toNat] at *
    omega⟩⟩

/-- Read UInt64 from 8 bytes (little-endian). -/
def UInt64.fromBytes' (f : Fin 8 → UInt8) : UInt64 :=
  assembleByte64 (f ⟨0, by omega⟩) (f ⟨1, by omega⟩)
    (f ⟨2, by omega⟩) (f ⟨3, by omega⟩)
    (f ⟨4, by omega⟩) (f ⟨5, by omega⟩)
    (f ⟨6, by omega⟩) (f ⟨7, by omega⟩)

/-- Write UInt64 to 8 bytes (little-endian). -/
def UInt64.toBytes' (v : UInt64) : Fin 8 → UInt8 := fun i =>
  match i with
  | ⟨0, _⟩ => ⟨⟨v.toNat % 256, by omega⟩⟩
  | ⟨1, _⟩ => ⟨⟨v.toNat / 256 % 256, by omega⟩⟩
  | ⟨2, _⟩ => ⟨⟨v.toNat / 65536 % 256, by omega⟩⟩
  | ⟨3, _⟩ => ⟨⟨v.toNat / 16777216 % 256, by omega⟩⟩
  | ⟨4, _⟩ => ⟨⟨v.toNat / 4294967296 % 256, by omega⟩⟩
  | ⟨5, _⟩ => ⟨⟨v.toNat / 1099511627776 % 256, by omega⟩⟩
  | ⟨6, _⟩ => ⟨⟨v.toNat / 281474976710656 % 256, by omega⟩⟩
  | ⟨7, _⟩ => ⟨⟨v.toNat / 72057594037927936 % 256, by omega⟩⟩

/-- Byte decomposition for UInt64. -/
private theorem byte_decompose64 (n : Nat) (hn : n < 18446744073709551616) :
    n % 256 + n / 256 % 256 * 256 + n / 65536 % 256 * 65536
    + n / 16777216 % 256 * 16777216
    + n / 4294967296 % 256 * 4294967296
    + n / 1099511627776 % 256 * 1099511627776
    + n / 281474976710656 % 256 * 281474976710656
    + n / 72057594037927936 % 256 * 72057594037927936 = n := by
  have h1 : n % 256 + 256 * (n / 256) = n := Nat.mod_add_div n 256
  have h2 : n / 256 % 256 + 256 * (n / 256 / 256) = n / 256 :=
    Nat.mod_add_div (n / 256) 256
  have h3 : n / 256 / 256 % 256 + 256 * (n / 256 / 256 / 256) = n / 256 / 256 :=
    Nat.mod_add_div (n / 256 / 256) 256
  have h4 : n / 256 / 256 / 256 % 256 + 256 * (n / 256 / 256 / 256 / 256) =
    n / 256 / 256 / 256 := Nat.mod_add_div (n / 256 / 256 / 256) 256
  have h5 : n / 256 / 256 / 256 / 256 % 256 + 256 * (n / 256 / 256 / 256 / 256 / 256) =
    n / 256 / 256 / 256 / 256 := Nat.mod_add_div (n / 256 / 256 / 256 / 256) 256
  have h6 : n / 256 / 256 / 256 / 256 / 256 % 256 +
    256 * (n / 256 / 256 / 256 / 256 / 256 / 256) =
    n / 256 / 256 / 256 / 256 / 256 := Nat.mod_add_div (n / 256 / 256 / 256 / 256 / 256) 256
  have h7 : n / 256 / 256 / 256 / 256 / 256 / 256 % 256 +
    256 * (n / 256 / 256 / 256 / 256 / 256 / 256 / 256) =
    n / 256 / 256 / 256 / 256 / 256 / 256 :=
    Nat.mod_add_div (n / 256 / 256 / 256 / 256 / 256 / 256) 256
  have h8 : n / 256 / 256 / 256 / 256 / 256 / 256 / 256 < 256 := by omega
  have h9 : n / 256 / 256 / 256 / 256 / 256 / 256 / 256 % 256 =
    n / 256 / 256 / 256 / 256 / 256 / 256 / 256 := Nat.mod_eq_of_lt h8
  -- Rewrite nested divisions to flat divisions
  have d2 : n / 256 / 256 = n / 65536 := by omega
  have d3 : n / 256 / 256 / 256 = n / 16777216 := by omega
  have d4 : n / 256 / 256 / 256 / 256 = n / 4294967296 := by omega
  have d5 : n / 256 / 256 / 256 / 256 / 256 = n / 1099511627776 := by omega
  have d6 : n / 256 / 256 / 256 / 256 / 256 / 256 = n / 281474976710656 := by omega
  have d7 : n / 256 / 256 / 256 / 256 / 256 / 256 / 256 = n / 72057594037927936 := by omega
  omega

theorem UInt64.fromBytes_toBytes' (v : UInt64) :
    UInt64.fromBytes' (UInt64.toBytes' v) = v := by
  have hv : v.toNat < 18446744073709551616 := v.toBitVec.isLt
  suffices h : (UInt64.fromBytes' (UInt64.toBytes' v)).toNat = v.toNat from
    UInt64.ext h
  show v.toNat % 256 + v.toNat / 256 % 256 * 256
    + v.toNat / 65536 % 256 * 65536
    + v.toNat / 16777216 % 256 * 16777216
    + v.toNat / 4294967296 % 256 * 4294967296
    + v.toNat / 1099511627776 % 256 * 1099511627776
    + v.toNat / 281474976710656 % 256 * 281474976710656
    + v.toNat / 72057594037927936 % 256 * 72057594037927936 = v.toNat
  exact byte_decompose64 v.toNat hv

instance : MemType UInt64 where
  size := 8
  align := 8
  typeTag := ⟨4⟩
  size_pos := by omega
  fromMem := UInt64.fromBytes'
  toMem := UInt64.toBytes'
  roundtrip := UInt64.fromBytes_toBytes'

/-! # Ptr MemType instance (8 bytes on x86-64 LP64)

Pointers are stored as 8-byte little-endian addresses.
We encode Ptr α as a UInt64 (the address), using the same
byte layout as UInt64. -/

/-- Read a Ptr from 8 bytes (little-endian address). -/
def Ptr.fromBytes' {α : Type} (f : Fin 8 → UInt8) : Ptr α :=
  let addr_nat := (UInt64.fromBytes' f).toNat
  ⟨⟨addr_nat % memSize, Nat.mod_lt _ (by unfold memSize; omega)⟩⟩

/-- Write a Ptr to 8 bytes (little-endian address). -/
def Ptr.toBytes' {α : Type} (p : Ptr α) : Fin 8 → UInt8 :=
  UInt64.toBytes' ⟨⟨p.addr.val, by
    have := p.addr.isLt; unfold memSize at this; omega⟩⟩

theorem Ptr.fromBytes_toBytes' {α : Type} (p : Ptr α) :
    Ptr.fromBytes' (Ptr.toBytes' p) = p := by
  simp only [Ptr.fromBytes', Ptr.toBytes']
  have hbound : p.addr.val < memSize := p.addr.isLt
  -- Show the UInt64 roundtrip preserves the Nat value
  -- First, the UInt64 we construct
  let u64 : UInt64 := ⟨⟨p.addr.val, by unfold memSize at hbound; omega⟩⟩
  -- After roundtrip, u64 is preserved
  have key : UInt64.fromBytes' (UInt64.toBytes' u64) = u64 :=
    UInt64.fromBytes_toBytes' u64
  -- So (UInt64.fromBytes' (UInt64.toBytes' u64)).toNat = u64.toNat = p.addr.val
  have hnat : u64.toNat = p.addr.val := by
    simp only [u64, UInt64.toNat]
    rfl
  have key2 : (UInt64.fromBytes' (UInt64.toBytes' u64)).toNat = p.addr.val := by
    rw [key, hnat]
  -- mod memSize is identity
  have hmod : (UInt64.fromBytes' (UInt64.toBytes' u64)).toNat % memSize = p.addr.val := by
    rw [key2]; exact Nat.mod_eq_of_lt hbound
  show Ptr.mk ⟨_, _⟩ = p
  congr 1
  exact Fin.ext hmod

instance {α : Type} [CType α] : CType (Ptr α) where
  size := 8
  align := 8
  typeTag := ⟨100 + (CType.typeTag (α := α)).id⟩  -- Encode "pointer to T" in tag
  size_pos := by omega

instance {α : Type} [CType α] : MemType (Ptr α) where
  size := 8
  align := 8
  typeTag := ⟨100 + (CType.typeTag (α := α)).id⟩
  size_pos := by omega
  fromMem := Ptr.fromBytes'
  toMem := Ptr.toBytes'
  roundtrip := Ptr.fromBytes_toBytes'

/-! # StructField descriptor and layout computation

Following gcc's x86-64 LP64 ABI rules:
- Each field is aligned to its natural alignment
- Struct alignment is the max alignment of all fields
- Struct size is padded to a multiple of struct alignment -/

/-- Descriptor for a single struct field. -/
structure StructField where
  /-- Field name (for documentation). -/
  name : String
  /-- Field size in bytes. -/
  size : Nat
  /-- Field alignment requirement. -/
  align : Nat
  /-- Computed byte offset within the struct. -/
  offset : Nat
  deriving Repr, DecidableEq

/-- Round up `n` to the next multiple of `a`. -/
def alignUp (n a : Nat) : Nat :=
  if a = 0 then n else ((n + a - 1) / a) * a

theorem alignUp_ge (n a : Nat) (ha : 0 < a) : n ≤ alignUp n a := by
  unfold alignUp
  split
  · omega
  · -- Need: n ≤ ((n + a - 1) / a) * a
    -- From Nat.div_add_mod: (n+a-1) = a * ((n+a-1)/a) + (n+a-1)%a
    -- So a * ((n+a-1)/a) = (n+a-1) - (n+a-1)%a ≥ n+a-1-(a-1) = n
    have h4 := Nat.div_add_mod (n + a - 1) a
    have h5 : (n + a - 1) % a < a := Nat.mod_lt _ (by omega)
    -- a * ((n+a-1)/a) ≥ n
    have h6 : a * ((n + a - 1) / a) ≥ n := by omega
    -- ((n+a-1)/a) * a = a * ((n+a-1)/a)
    have h7 : ((n + a - 1) / a) * a = a * ((n + a - 1) / a) := Nat.mul_comm _ _
    omega

/-- Compute struct layout: given a list of (size, alignment) pairs,
    return (fields with offsets, total struct size, struct alignment). -/
def computeStructLayout (fields : List (String × Nat × Nat)) :
    List StructField × Nat × Nat :=
  let result := fields.foldl (fun (acc : List StructField × Nat × Nat) (f : String × Nat × Nat) =>
    let (laid, curOffset, maxAlign) := acc
    let (name, sz, al) := f
    let offset := alignUp curOffset al
    let field := { name := name, size := sz, align := al, offset := offset : StructField }
    (laid ++ [field], offset + sz, max maxAlign al)
  ) ([], 0, 1)
  let (fields_out, rawSize, structAlign) := result
  -- Pad struct size to multiple of struct alignment
  let paddedSize := alignUp rawSize structAlign
  (fields_out, paddedSize, structAlign)

/-! # Pointer validity -/

/-- A pointer p is valid in heap state h when:
    1. The htd at p's address matches the type's tag
    2. The pointer is not null (addr ≠ 0)
    3. The pointer's range [addr, addr+size) fits in memory -/
def heapPtrValid {α : Type} [inst : CType α] (h : HeapRawState) (p : Ptr α) : Prop :=
  h.htd p.addr = some inst.typeTag ∧
  p.addr.val ≠ 0 ∧
  p.addr.val + inst.size ≤ memSize

/-- heapPtrValid is decidable (all components are decidable). -/
instance {α : Type} [inst : CType α] (h : HeapRawState) (p : Ptr α) :
    Decidable (heapPtrValid h p) := by
  unfold heapPtrValid
  exact instDecidableAnd

/-- heapPtrValid implies the address range fits in memory. -/
theorem heapPtrValid_bound {α : Type} [inst : CType α] {h : HeapRawState} {p : Ptr α}
    (hv : heapPtrValid h p) : p.addr.val + inst.size ≤ memSize :=
  hv.2.2

/-! # Memory slice operations -/

/-- Read `n` consecutive bytes from memory starting at `addr`.
    When addr + i overflows memSize, wraps via modular arithmetic.
    heapPtrValid ensures no wrapping occurs in practice. -/
def readMemSlice (mem : Fin memSize → UInt8) (addr : Nat) (n : Nat) :
    Fin n → UInt8 :=
  fun i => mem ⟨(addr + i.val) % memSize, Nat.mod_lt _ (by unfold memSize; omega)⟩

/-- Read `n` consecutive bytes from memory starting at `addr`.
    Version with bound proof: no modular wrapping needed. -/
def readMemSlice' (mem : Fin memSize → UInt8) (addr : Nat) (n : Nat)
    (_h_bound : addr + n ≤ memSize) :
    Fin n → UInt8 :=
  fun i => mem ⟨addr + i.val, by omega⟩

/-- readMemSlice and readMemSlice' agree when bound holds. -/
theorem readMemSlice_eq_readMemSlice'
    (mem : Fin memSize → UInt8) (addr : Nat) (n : Nat)
    (h_bound : addr + n ≤ memSize) :
    readMemSlice mem addr n = readMemSlice' mem addr n h_bound := by
  funext ⟨i, hi⟩
  simp only [readMemSlice, readMemSlice']
  congr 1
  apply Fin.ext
  simp
  exact Nat.mod_eq_of_lt (by omega)

/-- Write data to `n` consecutive bytes starting at `addr`.
    Overwrites [addr, addr+n), leaves all other addresses unchanged. -/
def writeMemSlice (mem : Fin memSize → UInt8) (addr : Nat) {n : Nat}
    (data : Fin n → UInt8)
    (_h_bound : addr + n ≤ memSize) :
    Fin memSize → UInt8 :=
  fun a =>
    if h : addr ≤ a.val ∧ a.val < addr + n then
      data ⟨a.val - addr, by omega⟩
    else
      mem a

/-! # Typed heap read/write -/

/-- Read a typed value from raw memory at a pointer's address.
    Total function — safe to use in CSimpl.basic.
    When the pointer is out of bounds, returns a garbage value
    (but heapPtrValid guards prevent this in practice). -/
def hVal {α : Type} [inst : MemType α] (h : HeapRawState) (p : Ptr α) : α :=
  inst.fromMem (readMemSlice h.mem p.addr.val inst.size)

/-- Read a typed value with explicit bound proof (for proofs). -/
def hVal' {α : Type} [inst : MemType α] (h : HeapRawState) (p : Ptr α)
    (h_bound : p.addr.val + inst.size ≤ memSize) : α :=
  inst.fromMem (readMemSlice' h.mem p.addr.val inst.size h_bound)

/-- hVal and hVal' agree when bound holds. -/
theorem hVal_eq_hVal' {α : Type} [inst : MemType α] (h : HeapRawState) (p : Ptr α)
    (h_bound : p.addr.val + inst.size ≤ memSize) :
    hVal h p = hVal' h p h_bound := by
  simp only [hVal, hVal']
  rw [readMemSlice_eq_readMemSlice' _ _ _ h_bound]

/-- Write a typed value to raw memory. Version with bound proof. -/
def heapUpdate' {α : Type} [inst : MemType α] (h : HeapRawState) (p : Ptr α) (v : α)
    (h_bound : p.addr.val + inst.size ≤ memSize) : HeapRawState :=
  { h with mem := writeMemSlice h.mem p.addr.val (inst.toMem v) h_bound }

/-- Write a typed value to raw memory at a pointer's address.
    Total function — safe to use in CSimpl.basic.
    When the pointer is out of bounds, returns the heap unchanged
    (but heapPtrValid guards prevent this in practice). -/
def heapUpdate {α : Type} [inst : MemType α] (h : HeapRawState) (p : Ptr α) (v : α) :
    HeapRawState :=
  if hb : p.addr.val + inst.size ≤ memSize then
    heapUpdate' h p v hb
  else h

/-- heapUpdate and heapUpdate' agree when bound holds. -/
theorem heapUpdate_eq_heapUpdate' {α : Type} [inst : MemType α]
    (h : HeapRawState) (p : Ptr α) (v : α)
    (h_bound : p.addr.val + inst.size ≤ memSize) :
    heapUpdate h p v = heapUpdate' h p v h_bound := by
  simp only [heapUpdate, dif_pos h_bound]

/-! # Core lemma: read after write at same pointer -/

theorem readMemSlice'_writeMemSlice_same
    (mem : Fin memSize → UInt8) (addr : Nat) {n : Nat}
    (data : Fin n → UInt8) (h_bound : addr + n ≤ memSize) :
    readMemSlice' (writeMemSlice mem addr data h_bound) addr n h_bound = data := by
  funext ⟨i, hi⟩
  simp only [readMemSlice', writeMemSlice]
  have h_in : addr ≤ addr + i ∧ addr + i < addr + n := by omega
  rw [dif_pos h_in]
  congr 1
  apply Fin.ext
  simp

/-- hVal' after heapUpdate' at the same pointer returns the written value. -/
theorem hVal'_heapUpdate'_same {α : Type} [inst : MemType α]
    (h : HeapRawState) (p : Ptr α) (v : α)
    (h_bound : p.addr.val + inst.size ≤ memSize) :
    hVal' (heapUpdate' h p v h_bound) p h_bound = v := by
  simp only [hVal', heapUpdate']
  rw [readMemSlice'_writeMemSlice_same]
  exact inst.roundtrip v

/-- hVal (total) after heapUpdate (total) at the same pointer returns the written value. -/
theorem hVal_heapUpdate_same {α : Type} [inst : MemType α]
    (h : HeapRawState) (p : Ptr α) (v : α)
    (h_bound : p.addr.val + inst.size ≤ memSize) :
    hVal (heapUpdate h p v) p = v := by
  rw [heapUpdate_eq_heapUpdate' _ _ _ h_bound, hVal_eq_hVal' _ _ h_bound]
  exact hVal'_heapUpdate'_same h p v h_bound

/-! # Disjoint write: read at different pointer unaffected -/

/-- Two pointers are disjoint when their byte ranges do not overlap. -/
def ptrDisjoint {α β : Type} [instA : CType α] [instB : CType β]
    (p : Ptr α) (q : Ptr β) : Prop :=
  p.addr.val + instA.size ≤ q.addr.val ∨ q.addr.val + instB.size ≤ p.addr.val

theorem readMemSlice'_writeMemSlice_disjoint
    (mem : Fin memSize → UInt8) (addr_w addr_r : Nat)
    {nw nr : Nat}
    (data : Fin nw → UInt8)
    (h_bound_w : addr_w + nw ≤ memSize)
    (h_bound_r : addr_r + nr ≤ memSize)
    (h_disj : addr_w + nw ≤ addr_r ∨ addr_r + nr ≤ addr_w) :
    readMemSlice' (writeMemSlice mem addr_w data h_bound_w) addr_r nr h_bound_r =
    readMemSlice' mem addr_r nr h_bound_r := by
  funext ⟨i, hi⟩
  simp only [readMemSlice', writeMemSlice]
  have h_out : ¬(addr_w ≤ addr_r + i ∧ addr_r + i < addr_w + nw) := by omega
  rw [dif_neg h_out]

/-- Reading at a disjoint pointer after a write returns the original value. -/
theorem hVal_heapUpdate_disjoint {α β : Type} [instA : MemType α] [instB : MemType β]
    (h : HeapRawState) (p : Ptr α) (q : Ptr β) (v : α)
    (h_bound_p : p.addr.val + instA.size ≤ memSize)
    (h_bound_q : q.addr.val + instB.size ≤ memSize)
    (h_disj : ptrDisjoint p q) :
    hVal (heapUpdate h p v) q = hVal h q := by
  rw [heapUpdate_eq_heapUpdate' _ _ _ h_bound_p]
  simp only [hVal_eq_hVal' _ _ h_bound_q, hVal', heapUpdate']
  rw [readMemSlice'_writeMemSlice_disjoint]
  exact h_disj

/-! # heapUpdate preserves htd and heapPtrValid -/

/-- heapUpdate only changes mem, not htd. -/
theorem heapUpdate_htd {α : Type} [inst : MemType α]
    (h : HeapRawState) (p : Ptr α) (v : α) :
    (heapUpdate h p v).htd = h.htd := by
  simp only [heapUpdate]
  split <;> simp [heapUpdate']

/-- heapUpdate preserves heapPtrValid for any pointer (same or different type). -/
theorem heapUpdate_preserves_heapPtrValid {α β : Type} [instA : MemType α] [instB : CType β]
    (h : HeapRawState) (p : Ptr α) (v : α) (q : Ptr β)
    (hv : heapPtrValid h q) :
    heapPtrValid (heapUpdate h p v) q := by
  unfold heapPtrValid at *
  rw [heapUpdate_htd]
  exact hv

/-! # ptrDisjoint symmetry -/

theorem ptrDisjoint_symm {α β : Type} [instA : CType α] [instB : CType β]
    {p : Ptr α} {q : Ptr β} (h : ptrDisjoint p q) :
    ptrDisjoint q p := by
  unfold ptrDisjoint at *
  omega

/-! # Global state infrastructure -/

/-- Base globals structure: raw heap + per-program global variables. -/
structure Globals where
  rawHeap : HeapRawState

/-! # CState: the full program state -/

/-- The full program state, parametric over a locals type.
    Following seL4's approach (plan.md Decision 3):
    - One Globals record for all functions
    - One Locals record for all functions (generated per-program)
    - CState combines both -/
structure CState (Locals : Type) where
  globals : Globals
  locals : Locals
