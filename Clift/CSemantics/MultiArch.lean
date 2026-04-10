-- MultiArch: Multi-architecture parameterization for word size, endianness, ABI
--
-- Task 0165: Make memSize, pointer size, endianness parameterizable.
-- Uses a typeclass so that all downstream code (CType, MemType, heap operations)
-- can be generic over the architecture.
--
-- Currently State.lean hardcodes `def memSize : Nat := 2^32`.
-- This module provides the parameterized alternative.
--
-- Design choice: typeclass over module parameter. A typeclass lets us
-- write architecture-generic lemmas and instantiate per-target. Module
-- parameters (sections with variables) would require explicit threading.

import Clift.CSemantics.TypeTag

/-! # Architecture configuration typeclass -/

/-- Endianness of byte encoding. -/
inductive Endianness where
  | little
  | big
  deriving Repr, DecidableEq

/-- Architecture configuration: everything that varies between targets.

    Instances exist for common targets (ARM32, ARM64, x86, x86_64, RISC-V).
    The CImporter's --arch flag selects the instance.

    All sizes are in bytes. All alignments are in bytes. -/
class ArchConfig where
  /-- Address space size in bytes. 2^32 for 32-bit, 2^64 for 64-bit. -/
  addrSpaceSize : Nat
  /-- Pointer size in bytes: 4 for 32-bit, 8 for 64-bit. -/
  pointerSize : Nat
  /-- Byte order for multi-byte values. -/
  endianness : Endianness
  /-- Natural alignment of int (bytes). Typically pointerSize. -/
  intAlign : Nat
  /-- Size of C `int` in bytes. -/
  intSize : Nat
  /-- Size of C `long` in bytes. Differs between LP64 and LLP64. -/
  longSize : Nat
  /-- Size of C `long long` in bytes. Always 8. -/
  longlongSize : Nat
  /-- Address space is positive (required for Fin). -/
  addrSpaceSize_pos : 0 < addrSpaceSize
  /-- Pointer size is positive. -/
  pointerSize_pos : 0 < pointerSize

/-! # Standard architecture instances -/

/-- ARM 32-bit, little-endian (ILP32 ABI). -/
instance : @ArchConfig where
  addrSpaceSize := 2^32
  pointerSize := 4
  endianness := .little
  intAlign := 4
  intSize := 4
  longSize := 4
  longlongSize := 8
  addrSpaceSize_pos := by omega
  pointerSize_pos := by omega

-- We define named configs as defs, not instances, to avoid ambiguity.
-- The user picks one via `attribute [local instance]` or explicit passing.

/-- ARM 32-bit, little-endian (ILP32). -/
@[reducible] def archARM32 : ArchConfig where
  addrSpaceSize := 2^32
  pointerSize := 4
  endianness := .little
  intAlign := 4
  intSize := 4
  longSize := 4
  longlongSize := 8
  addrSpaceSize_pos := by omega
  pointerSize_pos := by omega

/-- x86_64 / AMD64, little-endian (LP64). -/
@[reducible] def archX86_64 : ArchConfig where
  addrSpaceSize := 2^64
  pointerSize := 8
  endianness := .little
  intAlign := 4
  intSize := 4
  longSize := 8
  longlongSize := 8
  addrSpaceSize_pos := by omega
  pointerSize_pos := by omega

/-- ARM 64-bit (AArch64), little-endian (LP64). -/
@[reducible] def archARM64 : ArchConfig where
  addrSpaceSize := 2^64
  pointerSize := 8
  endianness := .little
  intAlign := 4
  intSize := 4
  longSize := 8
  longlongSize := 8
  addrSpaceSize_pos := by omega
  pointerSize_pos := by omega

/-- RISC-V 32-bit, little-endian (ILP32). -/
@[reducible] def archRISCV32 : ArchConfig where
  addrSpaceSize := 2^32
  pointerSize := 4
  endianness := .little
  intAlign := 4
  intSize := 4
  longSize := 4
  longlongSize := 8
  addrSpaceSize_pos := by omega
  pointerSize_pos := by omega

/-- RISC-V 64-bit, little-endian (LP64). -/
@[reducible] def archRISCV64 : ArchConfig where
  addrSpaceSize := 2^64
  pointerSize := 8
  endianness := .little
  intAlign := 4
  intSize := 4
  longSize := 8
  longlongSize := 8
  addrSpaceSize_pos := by omega
  pointerSize_pos := by omega

/-! # Architecture-parameterized memory types -/

/-- Parameterized memory size — replaces the hardcoded `def memSize`. -/
def archMemSize [cfg : ArchConfig] : Nat := cfg.addrSpaceSize

/-- Parameterized pointer type. -/
structure ArchPtr [cfg : ArchConfig] (α : Type) where
  addr : Fin cfg.addrSpaceSize
  deriving Repr

/-- Parameterized heap state. -/
structure ArchHeapRawState [cfg : ArchConfig] where
  mem : Fin cfg.addrSpaceSize → UInt8
  htd : Fin cfg.addrSpaceSize → Option TypeTag

/-! # Byte encoding with endianness -/

/-- Encode a Nat value as a list of bytes with the given endianness and width.
    Width is in bytes. Values are truncated to width bytes. -/
def encodeBytes (endian : Endianness) (width : Nat) (val : Nat) : List UInt8 :=
  let bytes := (List.range width).map (fun i => ((val >>> (i * 8)) % 256).toUInt8)
  match endian with
  | .little => bytes
  | .big => bytes.reverse

/-- Helper: decode little-endian byte list to Nat. -/
private def decodeBytesLE : List UInt8 → Nat → Nat
  | [], _ => 0
  | b :: rest, shift => b.toNat * (2 ^ shift) + decodeBytesLE rest (shift + 8)

/-- Decode a list of bytes to a Nat with the given endianness. -/
def decodeBytes (endian : Endianness) (bytes : List UInt8) : Nat :=
  let ordered := match endian with
    | .little => bytes
    | .big => bytes.reverse
  decodeBytesLE ordered 0

/-! # Example: same function verified for ARM32 and x86_64

The key insight: CSimpl terms and proofs are parameterized by ArchConfig.
A function verified with [ArchConfig] works for ANY architecture.
Architecture-specific properties (e.g., pointer size affects struct layout)
are resolved when the instance is selected.

```lean
-- Architecture-generic CSimpl term
def myFunc [ArchConfig] : CSimpl (ArchHeapRawState) := ...

-- Prove a property generically
theorem myFunc_correct [cfg : ArchConfig] : ... := ...

-- Instantiate for ARM32
example : ... := @myFunc_correct archARM32 ...

-- Instantiate for x86_64
example : ... := @myFunc_correct archX86_64 ...
```

## CImporter integration

The CImporter takes `--arch <target>` and:
1. Selects the appropriate clang target triple for `-target`
2. Emits `attribute [local instance] archARM32` (or whichever)
3. Uses the arch's sizes for struct layout computation
4. Verifiers can re-verify for a different arch by changing the instance

## Limitations

- Big-endian targets are defined but not tested (no big-endian CI).
- Struct layout ABI differences (e.g., bitfield packing) are not yet modeled.
- The default instance is ARM32 to match existing code. To use x86_64,
  add `attribute [local instance] archX86_64` in your file.
-/
