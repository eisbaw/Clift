-- Proof for rb_equal_validHoare (split from RBExtProofsSorry for memory)
import Examples.RBExtSpecs
set_option maxHeartbeats 25600000
set_option maxRecDepth 4096
open RingBufferExt

attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem rb_equal_validHoare :
    rb_equal_spec.satisfiedBy RingBufferExt.l1_rb_equal_body := by
  sorry
