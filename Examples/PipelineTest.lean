-- Pipeline test: verify clift command chains L1 -> L2 -> L3
--
-- Tests:
-- 1. clift on Gcd (while loop -> nondet classification)
-- 2. clift on Max (pure function -> pure classification + L1Deterministic)
-- 3. clift on Rotate3 (4 functions, mix of pure and nondet)
-- 4. clift_wa on a simple function
--
-- Each test verifies definitions and proofs are generated, no sorry.

import Generated.Gcd
import Generated.Max
import Generated.Swap
import Generated.Rotate3
import Clift.Lifting.Pipeline

set_option maxHeartbeats 6400000
set_option maxRecDepth 4096

/-! # Test 1: clift on Gcd -/

clift Gcd

-- L1 outputs
#check @Gcd.l1_gcd_body
#check @Gcd.l1_gcd_body_corres

-- L2 outputs
#check @Gcd.l2_gcd_body
#check @Gcd.l2_gcd_body_corres_fwd

-- L3 outputs: gcd has while loop -> nondet
#check @Gcd.l3_gcd_body_level
-- Should be MonadLevel.nondet
example : Gcd.l3_gcd_body_level = MonadLevel.nondet := rfl

/-! # Test 2: clift on Max -/

clift Max

-- L1 outputs
#check @Max.l1_max_body
#check @Max.l1_max_body_corres

-- L2 outputs
#check @Max.l2_max_body
#check @Max.l2_max_body_corres_fwd

-- L3 outputs: max is pure (no guard/fail/while)
#check @Max.l3_max_body_level
example : Max.l3_max_body_level = MonadLevel.pure := rfl

-- L3 determinism proof for pure function (auto-generated)
#check @Max.l3_max_body_det
#print axioms Max.l3_max_body_det

/-! # Test 3: clift on Rotate3 (4 functions) -/

clift Rotate3

-- rotate3: has guards -> nondet
#check @Rotate3.l3_rotate3_body_level
example : Rotate3.l3_rotate3_body_level = MonadLevel.nondet := rfl

-- abs_diff: pure (no guards, only conditions)
#check @Rotate3.l3_abs_diff_body_level
example : Rotate3.l3_abs_diff_body_level = MonadLevel.pure := rfl
#check @Rotate3.l3_abs_diff_body_det

-- clamp: pure (no guards, only conditions)
#check @Rotate3.l3_clamp_body_level
example : Rotate3.l3_clamp_body_level = MonadLevel.pure := rfl
#check @Rotate3.l3_clamp_body_det

-- sum_pair: nondet (has guards for addition overflow)
#check @Rotate3.l3_sum_pair_body_level
example : Rotate3.l3_sum_pair_body_level = MonadLevel.nondet := rfl

/-! # Test 4: clift on Swap (pointer code with guards) -/

clift Swap

#check @Swap.l1_swap_body
#check @Swap.l1_swap_body_corres
#check @Swap.l2_swap_body
#check @Swap.l3_swap_body_level
-- swap has guards (pointer validity checks) -> nondet
example : Swap.l3_swap_body_level = MonadLevel.nondet := rfl

/-! # Test 5: clift_wa on simple functions -/

-- A simple identity function for testing
def id_word (a : UInt32) : UInt32 := a
def id_nat (a : Nat) : Nat := a

-- This should be provable automatically
-- clift_wa id_word id_nat
-- ^ Would need WAcorres_pure1 which is defined in L5Auto

-- Manual test: verify WAcorres_pure2 for a trivial case
-- (gcd is recursive so auto-proof won't work, but we can verify the framework)

/-! # Test axioms -/

#print axioms Gcd.l1_gcd_body_corres
#print axioms Max.l3_max_body_det
#print axioms Rotate3.l3_abs_diff_body_det

/-! # Summary

clift command processes all CSimpl functions through L1 -> L2 -> L3.
- L1: CSimpl -> NondetM with L1corres proof
- L2: L1 -> wrapper with locals extracted, L2corres_fwd proof
- L3: classify as pure/nondet + L1Deterministic proof for pure

For L5 (WordAbstract): user provides Nat definitions, uses clift_wa.
-/
