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
