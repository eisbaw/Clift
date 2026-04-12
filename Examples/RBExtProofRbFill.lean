-- Proof for rb_fill_validHoare (split from RBExtProofsSorry for memory)
import Examples.RBExtSpecs
set_option maxHeartbeats 25600000
set_option maxRecDepth 4096
open RingBufferExt

attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem rb_fill_validHoare :
    rb_fill_spec.satisfiedBy RingBufferExt.l1_rb_fill_body := by
  sorry
