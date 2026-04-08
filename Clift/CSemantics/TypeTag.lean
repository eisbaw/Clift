-- Type tags and CType/MemType typeclasses for struct layout
--
-- Phase 0: minimal definitions. Extended in Phase 3 with full CType/MemType.
-- TypeTag identifies what type is stored at a given memory address.
-- Used by HeapRawState.htd (heap type descriptor).

/-- Opaque type identifier for heap type tracking.
    In Phase 3, this will be connected to CType/MemType typeclasses.
    For now, it is just a natural number identifier. -/
structure TypeTag where
  id : Nat
  deriving DecidableEq, Repr
