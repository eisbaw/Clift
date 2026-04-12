-- Proof for rb_clear_validHoare (split from RBExtProofsSorry for memory)
-- Status: WORK IN PROGRESS - helper lemmas proven, main theorem sorry
--
-- Architecture:
-- - rb_clear has a loop that mutates the heap (sets each node.next = null),
--   then resets rb.head/tail/count via 3 guard+modify pairs.
-- - This is a "heap+loop" proof (the hardest category, ~200-300 lines).
-- - The key challenge: proving LinkedListValid/WellFormedList is preserved
--   through heapUpdate at same-type pointers requires pairwise disjointness.
-- - We introduced WellFormedList (in RBExtSpecs.lean) which extends LinkedListValid
--   with pairwise byte-disjointness of consecutive nodes.
-- - The spec precondition uses WellFormedList instead of LinkedListValid.
--
-- Proven in this file:
-- - AllDisjointFrom_heapUpdate_frame: frame lemma for AllDisjointFrom through heapUpdate
-- - WellFormedList_heapUpdate_aux: WellFormedList preserved through heapUpdate at disjoint ptr
-- - WellFormedList_heapUpdate_tail: the tail of a WellFormedList is preserved through heapUpdate at head
--
-- Remaining work:
-- - Main theorem body: L1_hoare_catch decomposition, while loop invariant,
--   post-loop chain with hVal_heapUpdate_same for head/tail/count.

import Examples.RBExtSpecs
set_option maxHeartbeats 25600000
set_option maxRecDepth 4096
open RingBufferExt

/-! # Helper lemmas: WellFormedList preserved through heapUpdate -/

attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem AllDisjointFrom_heapUpdate_frame
    {heap : HeapRawState} {q r : Ptr C_rb_node} {v : C_rb_node} {p : Ptr C_rb_node}
    (hadj_q : AllDisjointFrom heap q p) (hadj_r : AllDisjointFrom heap r p)
    (hr : heapPtrValid heap r)
    : AllDisjointFrom (heapUpdate heap r v) q p := by
  induction hadj_q with
  | null => exact AllDisjointFrom.null
  | cons p' hp' hv' hdisj_qp' _ ih =>
    exact AllDisjointFrom.cons p' hp'
      (heapUpdate_preserves_heapPtrValid heap r v p' hv') hdisj_qp'
      (hVal_heapUpdate_disjoint heap r p' v (heapPtrValid_bound hr)
        (heapPtrValid_bound hv') (hadj_r.headDisjoint hp') ▸ ih (hadj_r.adjtail hp'))

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem WellFormedList_heapUpdate_aux
    {heap : HeapRawState} {p : Ptr C_rb_node} {v : C_rb_node} {nxt : Ptr C_rb_node}
    (hwf : WellFormedList heap nxt) (hv : heapPtrValid heap p)
    (h_sep : AllDisjointFrom heap p nxt)
    : WellFormedList (heapUpdate heap p v) nxt := by
  induction hwf with
  | null => exact WellFormedList.null
  | @cons q hq hv_q _ hsep_q ih =>
    have h_eq_q := hVal_heapUpdate_disjoint heap p q v (heapPtrValid_bound hv)
      (heapPtrValid_bound hv_q) (h_sep.headDisjoint hq)
    exact WellFormedList.cons q hq (heapUpdate_preserves_heapPtrValid heap p v q hv_q)
      (h_eq_q ▸ ih (h_sep.adjtail hq))
      (h_eq_q ▸ AllDisjointFrom_heapUpdate_frame hsep_q (h_sep.adjtail hq) hv)

attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem WellFormedList_heapUpdate_tail
    {heap : HeapRawState} {p : Ptr C_rb_node} {v : C_rb_node}
    (h : WellFormedList heap p) (hp : p ≠ Ptr.null) (hv : heapPtrValid heap p)
    : WellFormedList (heapUpdate heap p v) (hVal heap p).next :=
  WellFormedList_heapUpdate_aux (h.wf_tail hp) hv (h.headSep hp)

/-! # Main theorem -/

set_option maxRecDepth 16384 in
set_option maxHeartbeats 102400000 in
attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem rb_clear_validHoare :
    rb_clear_spec_ext.satisfiedBy RingBufferExt.l1_rb_clear_body := by
  unfold FuncSpec.satisfiedBy rb_clear_spec_ext
  unfold RingBufferExt.l1_rb_clear_body
  sorry
