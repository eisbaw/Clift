-- Rotate3: auto-generated L1 bodies via clift
--
-- Tests clift pipeline on rotate3, abs_diff, and clamp functions.
-- All L1 bodies + L1corres proofs are auto-generated.

import Generated.Rotate3
import Clift.Lifting.Pipeline

set_option maxHeartbeats 6400000
set_option maxRecDepth 4096

/-! # Run clift to auto-generate L1 bodies + L1corres proofs -/

clift Rotate3

open Rotate3

-- Verify auto-generated definitions exist
#check @Rotate3.l1_rotate3_body
#check @Rotate3.l1_abs_diff_body
#check @Rotate3.l1_clamp_body
#check @Rotate3.l1_rotate3_body_corres
#check @Rotate3.l1_abs_diff_body_corres
#check @Rotate3.l1_clamp_body_corres

/-! # Axiom audit -/

#print axioms Rotate3.l1_rotate3_body_corres
#print axioms Rotate3.l1_abs_diff_body_corres
#print axioms Rotate3.l1_clamp_body_corres
