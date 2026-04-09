-- c_vcg: verification condition generator for L1 monadic computations
--
-- Applies L1 Hoare rules compositionally to decompose validHoare goals
-- into leaf obligations about individual guards and modifications.
--
-- Supported L1 combinators:
--   L1.catch body handler  -> L1_hoare_catch_ok (when body is ok-only)
--                          -> L1_hoare_catch (general case)
--   L1.seq m₁ m₂           -> L1_hoare_seq_ok (when m₁ is ok-only)
--   L1.guard p              -> L1_hoare_guard'
--   L1.modify f             -> L1_hoare_modify'
--   L1.skip                 -> L1_hoare_skip
--   L1.throw                -> (produces error, handled by seq/catch)
--
-- The tactic produces flat proof terms that avoid deep kernel recursion.
-- Each rule produces `r = Except.ok () ∧ R s` shaped postconditions,
-- which compose without nesting match expressions.
--
-- Reference: L1HoareRules.lean for the underlying theorems.

import Clift.Lifting.L1HoareRules

/-! # c_vcg tactic: L1 verification condition generator

The tactic decomposes `validHoare P body Q` goals for L1 monadic
programs into leaf proof obligations. It applies L1 Hoare rules
in a bottom-up fashion, generating intermediate conditions automatically.

Usage:
  `c_vcg` — apply one decomposition step
  `c_vcg_all` — apply decomposition steps repeatedly until stuck

The remaining leaf goals are typically of the form:
  `∀ s, P s → Q (f s)` — for modify operations
  `∀ s, P s → p s ∧ R s` — for guard operations

These are left for the user or can be closed with `intro; simp; ...` -/

/-- `c_vcg` tactic: apply one L1 Hoare rule to decompose a validHoare goal.
    Tries rules in order of specificity:
    1. L1_hoare_skip — for L1.skip
    2. L1_hoare_guard' — for L1.guard p (produces ok ∧ R form)
    3. L1_hoare_modify' — for L1.modify f (produces ok ∧ R form)
    4. L1_hoare_catch_ok — for L1.catch body handler (ok-only body)
    5. L1_hoare_catch — for L1.catch body handler (general)
    6. L1_hoare_seq_ok — for L1.seq m₁ m₂ (ok-only m₁)
    7. L1_hoare_seq — for L1.seq m₁ m₂ (general)
    8. L1_hoare_pre — pre-strengthening -/
syntax "c_vcg" : tactic

macro_rules
  | `(tactic| c_vcg) => `(tactic|
    first
    | apply L1_hoare_skip
    | apply L1_hoare_guard'
    | apply L1_hoare_modify'
    | apply L1_hoare_catch_ok
    | apply L1_hoare_catch
    | apply L1_hoare_seq_ok
    | apply L1_hoare_seq
    | fail "c_vcg: could not find applicable L1 Hoare rule"
    )

/-- `c_vcg_all` tactic: apply c_vcg repeatedly to decompose an L1 program
    into leaf obligations. Stops when no more L1 Hoare rules apply. -/
syntax "c_vcg_all" : tactic

macro_rules
  | `(tactic| c_vcg_all) => `(tactic| repeat c_vcg)

/-! # c_vcg_leaf: discharge common leaf goals

After c_vcg_all decomposes the program, leaf goals typically look like:
- `validHoare P m Q` where m is a primitive (guard/modify/skip)
- Pre-condition implications: `P s → Q s`

c_vcg_leaf tries to close these with intro + simp + constructor tactics. -/

/-- `c_vcg_leaf` tactic: try to close a leaf goal from c_vcg decomposition.
    Uses intro, And.intro, simp, exact, assumption, and constructor. -/
syntax "c_vcg_leaf" : tactic

macro_rules
  | `(tactic| c_vcg_leaf) => `(tactic|
    first
    | (intro s hs; exact hs)
    | (intro s hs; obtain ⟨h1, h2⟩ := hs; exact ⟨h1, h2⟩)
    | assumption
    | constructor <;> assumption
    | (intro s hs; simp_all)
    )

/-- `c_vcg_finish` tactic: apply c_vcg_all then try c_vcg_leaf on all goals. -/
syntax "c_vcg_finish" : tactic

macro_rules
  | `(tactic| c_vcg_finish) => `(tactic| c_vcg_all <;> try c_vcg_leaf)
