-- Phase 3c: Manual HeapLift correspondence for swap
--
-- This file demonstrates the HeapLift layer (L4) for swap by manually
-- showing that raw heap operations (hVal, heapUpdate) correspond to
-- simpleLift-level operations.
--
-- The key correspondence: the L1 swap body performs hVal reads and
-- heapUpdate writes on the raw heap. At the simpleLift level, these
-- become simpleLift reads and simpleUpdate writes, with the sep-logic
-- swap_sep_correct theorem proving the postcondition.
--
-- For Phase 3, this is manual. Phase 4 MetaM will automate this
-- translation.

import Generated.Swap
import Clift.Lifting.HeapLift.SepLogic
import Clift.Lifting.HeapLift.SplitHeap

set_option maxHeartbeats 1600000

open Swap

/-! # HeapLift correspondence: raw heap swap → simpleLift swap

    The L1 swap body does:
    1. t := hVal h a        (read *a)
    2. h' := heapUpdate h a (hVal h b)   (write *a := *b)
    3. h'' := heapUpdate h' b t           (write *b := t = old *a)

    At the simpleLift level, this is:
    1. simpleLift h a = some va
    2. simpleUpdate h a vb
    3. simpleUpdate (simpleUpdate h a vb) b va

    The correspondence says: if the raw heap operations produce a
    final heap h_final, then simpleLift h_final agrees with the
    sep-logic postcondition (a ↦ vb, b ↦ va). -/

/-- The raw heap swap computation, expressed as a pure function.
    Given valid disjoint pointers a, b, produces the final heap. -/
noncomputable def rawSwapHeap (h : HeapRawState) (a b : Ptr UInt32) : HeapRawState :=
  let va := hVal h a
  let vb := hVal h b
  let h1 := heapUpdate h a vb
  heapUpdate h1 b va

/-- The simpleLift-level swap computation.
    Identical to rawSwapHeap but using simpleUpdate naming. -/
noncomputable def liftedSwapHeap (h : HeapRawState) (a b : Ptr UInt32) : HeapRawState :=
  let va := hVal h a
  let vb := hVal h b
  let h1 := simpleUpdate h a vb
  simpleUpdate h1 b va

/-- rawSwapHeap and liftedSwapHeap are definitionally equal.
    This is trivial because simpleUpdate = heapUpdate. -/
theorem rawSwap_eq_liftedSwap (h : HeapRawState) (a b : Ptr UInt32) :
    rawSwapHeap h a b = liftedSwapHeap h a b := by
  rfl

/-! # HeapLift correspondence theorem for swap

    The main result: if the precondition holds at the raw heap level
    (pointers valid, disjoint, values known), then the raw swap heap
    satisfies the sep-logic postcondition at the simpleLift level. -/

/-- HeapLift correspondence for swap: raw heap operations satisfy
    the separation logic specification via simpleLift.

    Pre:  mapsTo a va h ∧ mapsTo b vb h ∧ ptrDisjoint a b
    Post: mapsTo a vb h' ∧ mapsTo b va h' ∧ ptrDisjoint a b
    where h' = rawSwapHeap h a b -/
theorem swap_heapLift_corres (h : HeapRawState) (a b : Ptr UInt32) (va vb : UInt32)
    (h_pre : sepMapsTo a va b vb h) :
    sepMapsTo a vb b va (rawSwapHeap h a b) := by
  -- rawSwapHeap = liftedSwapHeap (definitionally)
  -- liftedSwapHeap = simpleUpdate (simpleUpdate h a vb) b va
  -- This is exactly what swap_sep_correct proves.
  show sepMapsTo a vb b va (liftedSwapHeap h a b)
  unfold liftedSwapHeap
  -- Extract values from precondition
  have ⟨h_ma, h_mb, h_disj⟩ := h_pre
  have hva_eq : hVal h a = va := h_ma.2
  have hvb_eq : hVal h b = vb := h_mb.2
  rw [hva_eq, hvb_eq]
  exact swap_sep_correct h a b va vb h_pre

/-! # Frame preservation: raw swap doesn't touch other pointers -/

/-- Any pointer disjoint from both a and b is unchanged by rawSwapHeap. -/
theorem swap_heapLift_frame {β : Type} [MemType β]
    (h : HeapRawState) (a b : Ptr UInt32) (va vb : UInt32)
    (r : Ptr β) (vr : β)
    (h_pre : sepMapsTo a va b vb h)
    (h_mr : mapsTo r vr h)
    (h_disj_a : ptrDisjoint a r)
    (h_disj_b : ptrDisjoint b r) :
    mapsTo r vr (rawSwapHeap h a b) := by
  show mapsTo r vr (liftedSwapHeap h a b)
  unfold liftedSwapHeap
  have hva_eq : hVal h a = va := h_pre.1.2
  have hvb_eq : hVal h b = vb := h_pre.2.1.2
  rw [hva_eq, hvb_eq]
  exact mapsTo_frame_swap h a vb b va r vr h_mr h_disj_a h_disj_b

/-! # SimpleLift readback: after raw swap, simpleLift returns swapped values -/

/-- After raw swap, simpleLift at a returns the old value of b. -/
theorem swap_simpleLift_a (h : HeapRawState) (a b : Ptr UInt32) (va vb : UInt32)
    (h_pre : sepMapsTo a va b vb h) :
    simpleLift (rawSwapHeap h a b) a = some vb := by
  have h_post := swap_heapLift_corres h a b va vb h_pre
  have ⟨hv_a, hval_a⟩ := h_post.1
  rw [simpleLift_val hv_a, hval_a]

/-- After raw swap, simpleLift at b returns the old value of a. -/
theorem swap_simpleLift_b (h : HeapRawState) (a b : Ptr UInt32) (va vb : UInt32)
    (h_pre : sepMapsTo a va b vb h) :
    simpleLift (rawSwapHeap h a b) b = some va := by
  have h_post := swap_heapLift_corres h a b va vb h_pre
  have ⟨hv_b, hval_b⟩ := h_post.2.1
  rw [simpleLift_val hv_b, hval_b]

#print axioms swap_heapLift_corres
#print axioms swap_heapLift_frame
#print axioms swap_simpleLift_a
#print axioms swap_simpleLift_b
