-- Proof for rb_reverse_validHoare (split from RBExtProofsSorry for memory)
import Examples.RBExtSpecs
set_option maxHeartbeats 25600000
set_option maxRecDepth 4096
open RingBufferExt

attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem rb_reverse_validHoare :
    rb_reverse_spec.satisfiedBy RingBufferExt.l1_rb_reverse_body := by
  sorry
