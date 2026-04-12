-- Proof for rb_clear_validHoare (split from RBExtProofsSorry for memory)
import Examples.RBExtSpecs
set_option maxHeartbeats 25600000
set_option maxRecDepth 4096
open RingBufferExt

attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem rb_clear_validHoare :
    rb_clear_spec.satisfiedBy RingBufferExt.l1_rb_clear_body := by
  sorry
