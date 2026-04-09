-- CStep tactic: unfold one monadic step and apply spec
--
-- Reference: ext/AutoCorres2/AutoCorresSimpset.thy
-- Inspired by Aeneas's `progress` tactic.
--
-- When invoked on a validHoare/totalHoare goal about a monadic bind,
-- c_step unfolds one bind step, applies the relevant Hoare rule
-- (hoare_seq, hoare_bind, hoare_basic, etc.), and leaves the user
-- with remaining precondition obligations.
--
-- Phase 2: basic implementation using Lean 4 macro/tactic combinators.
-- Does not yet handle function spec lookup automatically.

import Clift.MonadLib

/-! # c_step tactic

The tactic works on goals of the form:
  validHoare P (m₁ >>= f) Q
  validHoare P (NondetM.seq m₁ m₂) Q
  validHoare P (NondetM.basic f) Q
  validHoare P (NondetM.cond c t e) Q

For each case, it applies the appropriate Hoare rule.
-/

/-- `c_step` tactic: unfold one monadic step in a Hoare triple goal.

    Tries the following in order:
    1. hoare_basic — for `NondetM.basic f`
    2. hoare_seq / hoare_seq' — for `NondetM.seq m₁ m₂`
    3. hoare_bind — for `m >>= f`
    4. hoare_cond — for `NondetM.cond c t e`
    5. hoare_skip — for `NondetM.skip`

    After applying the rule, the user is left with the remaining
    proof obligations (preconditions, postconditions for sub-steps). -/
syntax "c_step" : tactic

macro_rules
  | `(tactic| c_step) => `(tactic|
    first
    | apply hoare_basic
    | apply hoare_skip
    | apply hoare_seq'
    | apply hoare_seq
    | apply hoare_bind
    | apply hoare_cond
    | apply hoare_while
    | apply hoare_consequence <;> [skip; skip; skip]
    | fail "c_step: could not find applicable Hoare rule"
    )

/-- `c_steps` tactic: apply c_step repeatedly until no more progress. -/
syntax "c_steps" : tactic

macro_rules
  | `(tactic| c_steps) => `(tactic| repeat c_step)

/-- `c_unfold` tactic: unfold function definitions in a Hoare triple goal.
    Useful before c_step when the goal has opaque definitions. -/
syntax "c_unfold" (ppSpace ident)* : tactic

macro_rules
  | `(tactic| c_unfold $[$ids]*) => `(tactic| unfold $[$ids]*)
