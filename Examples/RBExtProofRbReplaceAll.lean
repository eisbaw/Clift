-- Proof for rb_replace_all_validHoare (split from RBExtProofsSorry for memory)
import Examples.RBExtSpecs
set_option maxHeartbeats 25600000
set_option maxRecDepth 4096
open RingBufferExt

attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem rb_replace_all_validHoare :
    rb_replace_all_spec.satisfiedBy RingBufferExt.l1_rb_replace_all_body := by
  sorry
