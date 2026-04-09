-- Typed split heap: lightweight abstraction for Phase 3
--
-- Reference: ext/AutoCorres2/Split_Heap.thy
--
-- In AutoCorres, the "split heap" gives each C type its own logical heap
-- (Ptr α → Option α). This avoids reasoning about raw bytes and type tags
-- at the user proof level.
--
-- For Phase 3, we define a minimal typed heap state:
-- - TypedHeap α: a map from pointers to optional values
-- - Abstraction relation: TypedHeap agrees with simpleLift on all pointers
--
-- The split heap is NOT a new runtime structure. It is a proof-level
-- abstraction: we prove that simpleLift-based reasoning is equivalent to
-- reasoning about TypedHeap maps.

import Clift.Lifting.HeapLift.SimpleLift

/-! # Typed heap map -/

/-- A typed heap is a function from pointers to optional values.
    This is the per-type view of the raw heap after HeapLift. -/
def TypedHeap (α : Type) := Ptr α → Option α

/-! # Abstraction relation -/

/-- A TypedHeap agrees with the raw heap when simpleLift and the
    typed heap give the same result for every pointer.

    This is the state relation for HeapLift correspondence proofs:
    the concrete state uses HeapRawState, the abstract state uses TypedHeap. -/
def typedHeapAgrees {α : Type} [MemType α] (h : HeapRawState) (th : TypedHeap α) : Prop :=
  ∀ p : Ptr α, th p = simpleLift h p

/-- Construct a TypedHeap from a raw heap. This is the canonical lift. -/
noncomputable def typedHeapOf {α : Type} [MemType α] (h : HeapRawState) : TypedHeap α :=
  fun p => simpleLift h p

/-- The canonical typed heap agrees with its source. -/
theorem typedHeapOf_agrees {α : Type} [MemType α] (h : HeapRawState) :
    typedHeapAgrees h (typedHeapOf (α := α) h) :=
  fun _ => rfl

/-! # Typed heap update -/

/-- Update a typed heap at a single pointer. -/
def TypedHeap.update {α : Type} [DecidableEq (Ptr α)]
    (th : TypedHeap α) (p : Ptr α) (v : α) : TypedHeap α :=
  fun q => if q = p then some v else th q

/-- After a raw heap update at p, the canonical typed heap at p has the new value.
    Requires p to be valid (so the update and read succeed). -/
theorem typedHeapOf_update_same {α : Type} [MemType α]
    (h : HeapRawState) (p : Ptr α) (v : α) (hv : heapPtrValid h p) :
    (typedHeapOf (simpleUpdate h p v)) p = some v := by
  unfold typedHeapOf
  exact simpleLift_update_same h p v hv

/-- After a raw heap update at p, reading a disjoint pointer q is unchanged. -/
theorem typedHeapOf_update_disjoint {α β : Type} [MemType α] [MemType β]
    (h : HeapRawState) (p : Ptr α) (q : Ptr β) (v : α)
    (hv_q : heapPtrValid h q) (h_disj : ptrDisjoint p q) :
    typedHeapOf (simpleUpdate h p v) q = typedHeapOf h q := by
  unfold typedHeapOf
  exact simpleLift_update_disjoint h p q v hv_q h_disj
