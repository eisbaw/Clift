-- L1Auto + L2Auto test: verify automated CSimpl -> L1 -> L2 conversion
--
-- Tests clift_l1 on: gcd (while+guard), swap (guard+basic), max (cond),
-- rotate3 (guard chains), abs_diff (cond), clamp (nested cond)
--
-- Tests clift_l2 on: gcd, swap, max (wrapper-based L2 extraction)
--
-- Each test verifies:
-- 1. The definitions are generated
-- 2. The correspondence proofs are generated (no sorry)
-- 3. #print axioms shows no axioms beyond propositional extensionality

import Generated.Gcd
import Generated.Swap
import Generated.Max
import Generated.Rotate3
import Clift.Lifting.L1Auto
import Clift.Lifting.L2Auto

set_option maxHeartbeats 6400000
set_option maxRecDepth 4096

/-! # Test L1: gcd (while loop + guard) -/

clift_l1 Gcd

#check @Gcd.l1_gcd_body
#check @Gcd.l1_gcd_body_corres
#print axioms Gcd.l1_gcd_body_corres

/-! # Test L1: swap (pointer guards + heap operations) -/

clift_l1 Swap

#check @Swap.l1_swap_body
#check @Swap.l1_swap_body_corres
#print axioms Swap.l1_swap_body_corres

/-! # Test L1: max (simple cond) -/

clift_l1 Max

#check @Max.l1_max_body
#check @Max.l1_max_body_corres
#print axioms Max.l1_max_body_corres

/-! # Test L1: rotate3 + abs_diff + clamp + sum_pair -/

clift_l1 Rotate3

#check @Rotate3.l1_rotate3_body
#check @Rotate3.l1_rotate3_body_corres
#check @Rotate3.l1_abs_diff_body
#check @Rotate3.l1_abs_diff_body_corres
#check @Rotate3.l1_clamp_body
#check @Rotate3.l1_clamp_body_corres
#check @Rotate3.l1_sum_pair_body
#check @Rotate3.l1_sum_pair_body_corres

#print axioms Rotate3.l1_rotate3_body_corres
#print axioms Rotate3.l1_abs_diff_body_corres
#print axioms Rotate3.l1_clamp_body_corres
#print axioms Rotate3.l1_sum_pair_body_corres

/-! # Test L2: gcd -/

clift_l2 Gcd

#check @Gcd.l2_gcd_body
#check @Gcd.l2_gcd_body_corres_fwd
#print axioms Gcd.l2_gcd_body_corres_fwd

/-! # Test L2: swap -/

clift_l2 Swap

#check @Swap.l2_swap_body
#check @Swap.l2_swap_body_corres_fwd
#print axioms Swap.l2_swap_body_corres_fwd

/-! # Test L2: max -/

clift_l2 Max

#check @Max.l2_max_body
#check @Max.l2_max_body_corres_fwd
#print axioms Max.l2_max_body_corres_fwd

/-! # Test L2: rotate3 (all 4 functions) -/

clift_l2 Rotate3

#check @Rotate3.l2_rotate3_body
#check @Rotate3.l2_rotate3_body_corres_fwd
#check @Rotate3.l2_abs_diff_body
#check @Rotate3.l2_abs_diff_body_corres_fwd
#check @Rotate3.l2_clamp_body
#check @Rotate3.l2_clamp_body_corres_fwd
#check @Rotate3.l2_sum_pair_body
#check @Rotate3.l2_sum_pair_body_corres_fwd

#print axioms Rotate3.l2_rotate3_body_corres_fwd

/-! # Summary

L1 automation: 7 CSimpl functions across 4 modules converted automatically.
L2 automation: 7 L2 wrappers generated with forward correspondence proofs.

All proofs kernel-checked. Zero sorry.

L2 approach: wrapper-based extraction using l2_wrap.
- Locals become explicit function parameters
- State type is Globals (no locals record)
- Forward L2corres proved for each function
- validHoare transfers from L1 to L2 via l2_wrap_validHoare

Limitation: wrapper L2 fixes locals at function entry. The internal
computation still operates on full CState. A deeper L2 extraction
(fully eliminating locals from the computation) is future work. -/
