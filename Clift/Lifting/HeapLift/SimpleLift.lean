-- simpleLift: typed access to raw heap (following AutoCorres TypHeapSimple)
--
-- Reference: ext/AutoCorres2/TypHeapSimple.thy
-- Reference: plan.md Decision 8 (Phase 3 HeapLift)
--
-- simpleLift reads a typed value from the raw heap if the pointer is valid,
-- returning None otherwise. This is the key abstraction for HeapLift (L4):
-- it bridges raw bytes (HeapRawState) and typed heap access.
--
-- Restriction (same as AutoCorres): nested struct field access via sub-pointers
-- is NOT supported. You access structs as whole values.

import Clift.CSemantics.State

/-! # simpleLift: typed heap read -/

/-- Read a typed value from raw heap if pointer is valid, else None.
    Following AutoCorres2's simple_lift (TypHeapSimple.thy line 53-60).

    When `heapPtrValid h p` holds:
    - The htd at p's address matches the type tag
    - The pointer is non-null
    - The byte range fits in memory
    So we can safely read via `hVal`. -/
noncomputable def simpleLift {α : Type} [MemType α] (h : HeapRawState) (p : Ptr α) : Option α :=
  if heapPtrValid h p then some (hVal h p) else none

/-! # simpleUpdate: typed heap write at the lift layer

    Alias for heapUpdate — provided for symmetry with simpleLift.
    The raw heap write is already well-defined; we re-export it at
    this abstraction level so Phase 4 proofs use consistent naming. -/

noncomputable def simpleUpdate {α : Type} [MemType α] (h : HeapRawState) (p : Ptr α) (v : α) :
    HeapRawState :=
  heapUpdate h p v

/-! # simpleLift lemmas -/

/-- simpleLift returns Some iff the pointer is valid. -/
theorem simpleLift_some {α : Type} [MemType α] {h : HeapRawState} {p : Ptr α} {v : α}
    (hs : simpleLift h p = some v) : heapPtrValid h p := by
  unfold simpleLift at hs
  split at hs
  · assumption
  · cases hs

/-- When the pointer is valid, simpleLift returns the hVal. -/
theorem simpleLift_val {α : Type} [MemType α] {h : HeapRawState} {p : Ptr α}
    (hv : heapPtrValid h p) : simpleLift h p = some (hVal h p) := by
  unfold simpleLift
  simp [hv]

/-- When the pointer is not valid, simpleLift returns None. -/
theorem simpleLift_none {α : Type} [MemType α] {h : HeapRawState} {p : Ptr α}
    (hv : ¬ heapPtrValid h p) : simpleLift h p = none := by
  unfold simpleLift
  simp [hv]

/-- simpleLift after simpleUpdate at the same pointer returns the written value. -/
theorem simpleLift_update_same {α : Type} [MemType α]
    (h : HeapRawState) (p : Ptr α) (v : α)
    (hv : heapPtrValid h p) :
    simpleLift (simpleUpdate h p v) p = some v := by
  have hb := heapPtrValid_bound hv
  have hv' := heapUpdate_preserves_heapPtrValid h p v p hv
  unfold simpleLift simpleUpdate
  simp [hv']
  exact hVal_heapUpdate_same h p v hb

/-- simpleLift after simpleUpdate at a disjoint pointer is unchanged.
    Requires q to be valid (so simpleLift h q = some (hVal h q)).
    p need not be valid — if p is out of bounds, heapUpdate is identity. -/
theorem simpleLift_update_disjoint {α β : Type} [instA : MemType α] [MemType β]
    (h : HeapRawState) (p : Ptr α) (q : Ptr β) (v : α)
    (hv_q : heapPtrValid h q)
    (h_disj : ptrDisjoint p q) :
    simpleLift (simpleUpdate h p v) q = simpleLift h q := by
  unfold simpleUpdate
  -- Case split: does heapUpdate actually modify the heap?
  by_cases hbp : p.addr.val + instA.size ≤ memSize
  · -- p is in bounds: heapUpdate modifies memory but q reads are unaffected
    have hv_q' := heapUpdate_preserves_heapPtrValid h p v q hv_q
    unfold simpleLift
    simp [hv_q', hv_q]
    exact hVal_heapUpdate_disjoint h p q v hbp (heapPtrValid_bound hv_q) h_disj
  · -- p is out of bounds: heapUpdate is identity
    simp only [heapUpdate, dif_neg hbp]
