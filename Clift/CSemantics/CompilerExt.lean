-- CompilerExt: Compiler extensions — packed, aligned, volatile, builtins
--
-- Task 0168: Define Lean types for GCC/Clang compiler extensions used
-- in embedded C. For each extension, define the type and show how the
-- CImporter would emit it.
--
-- Extensions covered:
-- 1. packed structs: zero padding in CType layout
-- 2. aligned: forced alignment in CType
-- 3. volatile: reads as nondeterministic CSimpl.spec
-- 4. builtins: axiomatized with specs (__builtin_clz, etc.)

import Clift.CSemantics.CSimpl
import Clift.CSemantics.State

/-! # Packed structs -/

/-- Marker for packed struct layout.
    When `packed = true`, the CImporter computes struct layout with
    zero inter-field padding. Only tail padding for alignment may remain.

    In standard C: `__attribute__((packed))` -/
structure PackedAttr where
  packed : Bool := false

/-- Extended CType with packing and alignment attributes.
    This extends the base CType typeclass with GCC/Clang attributes. -/
class CTypeExt (α : Type) extends CType α where
  /-- Whether this type has __attribute__((packed)) -/
  isPacked : Bool := false
  /-- Explicit alignment override from __attribute__((aligned(N))).
      `none` means use the natural alignment from CType.align. -/
  explicitAlign : Option Nat := none
  /-- Effective alignment: explicit override or natural -/
  effectiveAlign : Nat := match explicitAlign with
    | some a => a
    | none => CType.align α

/-! ## Packed struct example

A packed struct has zero padding between fields:

```c
struct __attribute__((packed)) PackedExample {
    uint8_t  a;   // offset 0, size 1
    uint32_t b;   // offset 1, size 4 (NOT offset 4!)
    uint16_t c;   // offset 5, size 2
};  // total size: 7 bytes (not 8 or 12)
```

The CImporter computes field offsets by summing sizes without alignment padding:
-/

/-- Example packed struct. -/
structure PackedExample where
  a : UInt8
  b : UInt32
  c : UInt16

/-- CType instance for a packed struct: fields are contiguous, no padding. -/
instance : CType PackedExample where
  size := 7    -- 1 + 4 + 2, no padding
  align := 1   -- packed structs have alignment 1
  typeTag := ⟨100⟩  -- arbitrary ID for PackedExample
  size_pos := by omega

/-- CTypeExt instance marking it as packed. -/
instance : CTypeExt PackedExample where
  isPacked := true

/-- For comparison: the UNPACKED version would have:
    - a at offset 0 (1 byte) + 3 bytes padding
    - b at offset 4 (4 bytes)
    - c at offset 8 (2 bytes) + 2 bytes padding
    - total: 12 bytes, alignment 4 -/
structure UnpackedExample where
  a : UInt8
  b : UInt32
  c : UInt16

instance : CType UnpackedExample where
  size := 12
  align := 4
  typeTag := ⟨101⟩  -- arbitrary ID for UnpackedExample
  size_pos := by omega

/-! # Aligned attribute -/

/-- Example: forced alignment.

```c
struct __attribute__((aligned(64))) CacheLine {
    uint32_t data[16];
};
```

The `aligned(N)` attribute forces the struct's alignment to at least N.
It does NOT change the size of fields, only the alignment of the struct
itself (affecting placement in arrays and on the stack).
-/

structure CacheLineAligned where
  data : Fin 16 → UInt32

instance : CType CacheLineAligned where
  size := 64     -- 16 * 4
  align := 64    -- forced by __attribute__((aligned(64)))
  typeTag := ⟨102⟩  -- arbitrary ID for CacheLineAligned
  size_pos := by omega

instance : CTypeExt CacheLineAligned where
  explicitAlign := some 64

/-! # Volatile reads and writes -/

/-- A volatile read: the value may have been changed by hardware (MMIO)
    or by an ISR since the last write. Modeled as nondeterministic.

    `volatileRead proj update` reads a field from state, but the actual
    value is nondeterministic — any value satisfying `valid` may be returned.

    Parameters:
    - `valid`: constrains which values are possible (e.g., register bit widths)
    - `update`: writes the nondeterministic value into the state's local

    The CImporter emits this for `volatile T *p; ... = *p;` -/
def volatileRead {σ : Type} (valid : σ → σ → Prop) : CSimpl σ :=
  .spec valid

/-- A volatile write: the value is written but may have side effects
    visible only to hardware. Modeled as a basic write followed by
    a nondeterministic spec for hardware side effects.

    For MMIO: writing a register may trigger hardware actions that
    change OTHER registers. The `sideEffect` relation captures this.

    Parameters:
    - `write`: the deterministic write to the target address
    - `sideEffect`: what hardware may do in response

    The CImporter emits this for `*p = val;` where p is volatile. -/
def volatileWrite {σ : Type} (write : σ → σ) (sideEffect : σ → σ → Prop) : CSimpl σ :=
  .seq (.basic write) (.spec sideEffect)

/-- Simple volatile write with no side effects (shared memory, not MMIO).
    The write is deterministic but a subsequent read may see a different value
    (because an ISR might overwrite it). -/
def volatileWriteSimple {σ : Type} (write : σ → σ) : CSimpl σ :=
  .basic write

/-! ## Volatile example: MMIO register access

```c
volatile uint32_t *UART_STATUS = (volatile uint32_t *)0x40001000;
volatile uint32_t *UART_DATA   = (volatile uint32_t *)0x40001004;

void uart_send(uint8_t byte) {
    while (!(*UART_STATUS & TX_READY))  // volatile read, nondeterministic
        ;
    *UART_DATA = byte;                  // volatile write, may trigger HW
}
```
-/

/-- Example UART state for volatile modeling. -/
structure UartState where
  txReady : Bool
  txData : UInt8
  txCount : Nat  -- side effect: incremented by hardware on write

/-- Volatile read of UART status register. -/
def uartStatusRead : CSimpl UartState :=
  volatileRead (fun _s s' =>
    -- The read may return any state — txReady can be true or false.
    -- Hardware determines when the TX buffer is ready.
    s'.txData = _s.txData ∧ s'.txCount = _s.txCount)
    -- Only txReady may change (hardware sets it when buffer is free)

/-- Volatile write to UART data register with hardware side effect. -/
def uartDataWrite (byte : UInt8) : CSimpl UartState :=
  volatileWrite
    (fun s => { s with txData := byte })
    (fun s s' =>
      -- Hardware side effect: txCount incremented, txReady cleared
      s'.txCount = s.txCount + 1 ∧ s'.txReady = false ∧ s'.txData = s.txData)

/-! # Compiler builtins -/

/-- An axiomatized compiler builtin.
    Like AsmSpec but for compiler intrinsics that have well-defined
    semantics. The spec is trusted (enters TCB). -/
structure BuiltinSpec (σ : Type) where
  /-- Builtin name (e.g., "__builtin_clz") -/
  name : String
  /-- Precondition (e.g., argument != 0 for __builtin_clz) -/
  pre : σ → Prop
  /-- Postcondition: deterministic result, modeled as state update -/
  post : σ → σ → Prop
  /-- Documentation: what this builtin computes -/
  doc : String

namespace BuiltinSpec

variable {σ : Type}

/-- Convert a builtin spec to a CSimpl term.
    Same pattern as AsmSpec: guard pre, then spec post. -/
def toCSimpl (spec : BuiltinSpec σ) : CSimpl σ :=
  .guard spec.pre (.spec spec.post)

end BuiltinSpec

/-! ## Standard builtins -/

/-- Count leading zeros. Undefined if input is 0.

    __builtin_clz(x): returns the number of leading 0-bits in x,
    starting from the most significant bit position.
    If x is 0, the result is undefined (UB).

    We model the result as writing to a designated local variable. -/
def builtinClz {σ : Type} (getArg : σ → UInt32) (setResult : σ → UInt32 → σ) : BuiltinSpec σ where
  name := "__builtin_clz"
  pre := fun s => getArg s ≠ 0
  post := fun s s' =>
    -- Result is the number of leading zeros in the argument
    let arg := getArg s
    -- We axiomatize the result rather than computing it,
    -- because the computation is well-defined but tedious in Lean.
    ∃ result : UInt32,
      s' = setResult s result ∧
      -- The result is bounded: 0 <= clz < 32
      result.toNat < 32 ∧
      -- Key property: 2^(31 - clz) <= arg < 2^(32 - clz)
      -- (This is the defining property of CLZ)
      (result.toNat < 31 →
        2 ^ (31 - result.toNat) ≤ arg.toNat ∧ arg.toNat < 2 ^ (32 - result.toNat))
  doc := "Count leading zeros in a 32-bit integer. UB if argument is 0."

/-- Count trailing zeros. Undefined if input is 0. -/
def builtinCtz {σ : Type} (getArg : σ → UInt32) (setResult : σ → UInt32 → σ) : BuiltinSpec σ where
  name := "__builtin_ctz"
  pre := fun s => getArg s ≠ 0
  post := fun s s' =>
    let arg := getArg s
    ∃ result : UInt32,
      s' = setResult s result ∧
      result.toNat < 32 ∧
      -- Key property: arg is divisible by 2^ctz but not 2^(ctz+1)
      (arg.toNat % (2 ^ result.toNat) = 0) ∧
      (result.toNat < 31 → arg.toNat % (2 ^ (result.toNat + 1)) ≠ 0)
  doc := "Count trailing zeros in a 32-bit integer. UB if argument is 0."

/-- Population count (number of set bits). Always defined. -/
def builtinPopcount {σ : Type} (getArg : σ → UInt32) (setResult : σ → UInt32 → σ) : BuiltinSpec σ where
  name := "__builtin_popcount"
  pre := fun _ => True  -- always defined, even for 0
  post := fun s s' =>
    ∃ result : UInt32,
      s' = setResult s result ∧
      result.toNat ≤ 32
      -- Full specification would count bits, but for the framework
      -- we just bound the result. Users can add axioms for specific values.
  doc := "Count the number of set bits in a 32-bit integer."

/-- Byte swap (endianness conversion). Always defined. -/
def builtinBswap32 {σ : Type} (_getArg : σ → UInt32) (setResult : σ → UInt32 → σ) : BuiltinSpec σ where
  name := "__builtin_bswap32"
  pre := fun _ => True
  post := fun s s' =>
    ∃ result : UInt32,
      s' = setResult s result ∧
      -- bswap is its own inverse
      True  -- Full byte-level spec would go here
  doc := "Reverse the bytes of a 32-bit integer."

/-! # CImporter integration

## How the CImporter emits each extension

### Packed structs
```python
# In import.py, when processing a RecordDecl with packed attribute:
if has_attr(node, "packed"):
    # Compute offsets by summing sizes (no alignment padding)
    offset = sum(field_sizes[:i])
    # Emit CType with isPacked = true, align = 1
```

### Aligned attribute
```python
# In import.py, when processing aligned attribute:
if has_attr(node, "aligned"):
    n = get_attr_value(node, "aligned")
    # Emit CTypeExt with explicitAlign = some n
```

### Volatile
```python
# In import.py, when processing a DeclRefExpr with volatile qualifier:
if is_volatile(type):
    if is_read:
        # Emit volatileRead with appropriate valid relation
    else:
        # Emit volatileWrite with write function
```

### Builtins
```python
# In import.py, when processing a CallExpr to a known builtin:
BUILTIN_MAP = {
    "__builtin_clz": "builtinClz",
    "__builtin_ctz": "builtinCtz",
    "__builtin_popcount": "builtinPopcount",
    "__builtin_bswap32": "builtinBswap32",
}
if func_name in BUILTIN_MAP:
    # Emit BuiltinSpec.toCSimpl call
```

## What enters the TCB

- Packed/aligned: NOT in TCB. These are CType instances generated by the
  CImporter. If wrong, struct layout proofs won't go through.
- Volatile: NOT in TCB beyond the existing CImporter trust. The nondeterministic
  modeling is conservative (overapproximates possible behaviors).
- Builtins: IN TCB. The BuiltinSpec post-conditions are trusted.
  If wrong, proofs about code using builtins are unsound.
-/
