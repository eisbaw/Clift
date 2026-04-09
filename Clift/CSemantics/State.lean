-- State types: HeapRawState, Ptr, typed heap access
--
-- Phase 0-3a: memory model with typed read/write.
-- Extended in Phase 3c with HeapLift (typed split heaps).
--
-- Reference: plan.md Decision 8
-- Reference: ext/AutoCorres2/c-parser/umm_heap/HeapRawState.thy
-- Reference: ext/AutoCorres2/TypHeapSimple.thy

import Clift.CSemantics.TypeTag
import Mathlib.Data.Fin.Basic

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
  deriving DecidableEq, Repr

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

/-! # Pointer validity -/

/-- A pointer p is valid in heap state h when:
    1. The htd at p's address matches the type's tag
    2. The pointer is not null (addr ≠ 0)
    3. The pointer's range [addr, addr+size) fits in memory -/
def heapPtrValid {α : Type} [inst : CType α] (h : HeapRawState) (p : Ptr α) : Prop :=
  h.htd p.addr = some inst.typeTag ∧
  p.addr.val ≠ 0 ∧
  p.addr.val + inst.size ≤ memSize

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
