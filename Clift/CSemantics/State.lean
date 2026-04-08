-- State types: HeapRawState, Ptr
--
-- Phase 0: minimal definitions for the memory model.
-- Extended in Phase 3 with full typed heap lifting.
--
-- Reference: plan.md Decision 8 (Phase 1 MVP memory model)
-- Reference: ext/AutoCorres2/c-parser/umm_heap/HeapRawState.thy

import Clift.CSemantics.TypeTag

/-! # Memory model constants -/

/-- Memory size in bytes. Fixed for now; will become a parameter in Phase 3.
    Using 2^32 for a 32-bit address space. -/
def memSize : Nat := 2^32

/-! # Raw heap state -/

/-- Byte-level heap with type tracking.
    - `mem`: byte-addressed memory
    - `htd`: heap type descriptor — what type is stored at each address

    This is the Phase 1 MVP memory model (plan.md Decision 8).
    Phase 3 lifts this to typed split heaps via simpleLift. -/
structure HeapRawState where
  mem : Fin memSize → UInt8
  htd : Fin memSize → Option TypeTag

/-! # Typed pointer -/

/-- Pointer with phantom type tag.
    The type parameter α is phantom — it exists only for type safety
    in the Lean type system. The actual type stored at the address
    is tracked by HeapRawState.htd. -/
structure Ptr (α : Type) where
  addr : Fin memSize

/-! # CType typeclass skeleton -/

/-- Typeclass for C types that can be stored in the heap.
    Provides size and alignment information.
    Phase 0: skeleton only. Phase 3 adds full byte-level encode/decode. -/
class CType (α : Type) where
  /-- Size in bytes -/
  size : Nat
  /-- Alignment requirement in bytes (must be a power of 2) -/
  align : Nat
  /-- TypeTag for heap type descriptor tracking -/
  typeTag : TypeTag

/-- Typeclass for C types that can be read from/written to raw memory.
    Extends CType with encode/decode operations.
    Phase 0: skeleton only. Phase 3 provides actual implementations. -/
class MemType (α : Type) extends CType α where
  /-- Encode a value into bytes. Length must equal CType.size. -/
  encode : α → List UInt8
  /-- Decode bytes into a value. Input length must equal CType.size. -/
  decode : List UInt8 → Option α

/-- UInt32 CType instance for Phase 0 use. -/
instance : CType UInt32 where
  size := 4
  align := 4
  typeTag := ⟨1⟩

/-! # Global state infrastructure -/

/-- Base globals structure: raw heap + per-program global variables.
    The CImporter will generate a program-specific Globals structure.
    For Phase 0, this minimal version has only the raw heap. -/
structure Globals where
  rawHeap : HeapRawState

/-! # CState: the full program state -/

/-- The full program state, parametric over a locals type.
    Following seL4's approach (plan.md Decision 3):
    - One Globals record for all functions
    - One Locals record for all functions (generated per-program)
    - CState combines both

    The CImporter generates a concrete Locals type per program.
    For Phase 0, individual test files define their own state types
    (e.g., MaxState for max.c) — the CState pattern is demonstrated
    here for documentation. -/
structure CState (Locals : Type) where
  globals : Globals
  locals : Locals
