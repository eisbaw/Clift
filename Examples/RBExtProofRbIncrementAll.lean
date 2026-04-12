-- Proof for rb_increment_all_validHoare (split from RBExtProofsSorry for memory)
import Examples.RBExtSpecs
set_option maxHeartbeats 25600000
set_option maxRecDepth 4096
open RingBufferExt

attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem rb_increment_all_validHoare :
    rb_increment_all_spec.satisfiedBy RingBufferExt.l1_rb_increment_all_body := by
  sorry
