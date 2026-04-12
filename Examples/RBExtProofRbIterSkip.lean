-- Proof for rb_iter_skip_validHoare (split from RBExtProofsSorry for memory)
import Examples.RBExtSpecs
set_option maxHeartbeats 25600000
set_option maxRecDepth 4096
open RingBufferExt

attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem rb_iter_skip_validHoare :
    rb_iter_skip_spec.satisfiedBy RingBufferExt.l1_rb_iter_skip_body := by
  sorry
