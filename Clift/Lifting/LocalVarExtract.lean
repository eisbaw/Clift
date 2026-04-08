-- L2: Lift locals from state record into lambda-bound Lean variables + corres proof
--
-- Reference: ext/AutoCorres2/LocalVarExtract.thy, ext/AutoCorres2/L2Defs.thy
--
-- Phase 1: Manual L2 extraction for gcd.
-- After L2, local variables (a, b, t) are lambda-bound parameters,
-- not fields of the state record. The state contains only globals.
--
-- The L2 monad operates on a state WITHOUT locals. Locals become
-- explicit function parameters and return values.

import Clift.Lifting.SimplConv

set_option maxHeartbeats 1600000

/-! # L2 state type -/

-- After L2 extraction, the state has no locals.
-- For Phase 1 gcd, there are no globals used, so the state is trivial.
-- In general, L2 state = globals only.

/-! # L2corres: correspondence between L1 (with locals in state) and L2 (locals extracted) -/

-- L2corres relates an L1 computation (over full state with locals)
-- to an L2 computation (over reduced state, locals as parameters).
-- The key idea: there exists an abstraction function that projects
-- the full state to the reduced state, and the locals are captured
-- by the lambda binding.

-- For Phase 1, we demonstrate this manually for gcd.
-- The MetaM automation is Phase 2.
