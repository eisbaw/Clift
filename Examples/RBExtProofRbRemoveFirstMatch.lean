-- Proof for rb_remove_first_match_validHoare (split from RBExtProofsSorry for memory)
import Examples.RBExtSpecs
set_option maxHeartbeats 25600000
set_option maxRecDepth 4096
open RingBufferExt

attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem rb_remove_first_match_validHoare :
    rb_remove_first_match_spec.satisfiedBy RingBufferExt.l1_rb_remove_first_match_body := by
  sorry
