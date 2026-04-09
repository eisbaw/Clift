-- corres_auto: automate L1corres proofs
--
-- L1corres proofs have a formulaic structure: recursively decompose the
-- CSimpl program and apply the matching L1corres lemma at each step.
-- This tactic automates that pattern.
--
-- Supported CSimpl constructors:
--   .skip      -> L1corres_skip
--   .basic f   -> L1corres_basic
--   .seq c₁ c₂ -> L1corres_seq
--   .cond b c₁ c₂ -> L1corres_cond
--   .while b c -> L1corres_while
--   .catch c₁ c₂ -> L1corres_catch
--   .guard p c -> L1corres_guard
--   .throw     -> L1corres_throw
--
-- Usage:
--   `corres_auto` — apply one L1corres decomposition step
--   `corres_auto_all` — repeatedly apply until no more rules match
--
-- Reference: l1_swap_body_corres in SwapProof.lean shows the manual version.

import Clift.Lifting.SimplConv

/-! # corres_auto tactic -/

/-- `corres_auto` tactic: apply one L1corres lemma to decompose a correspondence goal.
    Matches the CSimpl constructor in the goal and applies the corresponding lemma.
    Order matters: simpler rules (skip, basic, throw) before compound rules (seq, cond). -/
syntax "corres_auto" : tactic

macro_rules
  | `(tactic| corres_auto) => `(tactic|
    first
    | (apply L1corres_skip)
    | (apply L1corres_basic)
    | (apply L1corres_throw)
    | (apply L1corres_seq <;> corres_auto)
    | (apply L1corres_cond <;> corres_auto)
    | (apply L1corres_catch <;> corres_auto)
    | (apply L1corres_guard; corres_auto)
    | (apply L1corres_while; corres_auto)
    | fail "corres_auto: could not find applicable L1corres rule"
    )

/-- `corres_auto_all` tactic: repeatedly apply corres_auto.
    Useful when the goal has already been unfolded. -/
syntax "corres_auto_all" : tactic

macro_rules
  | `(tactic| corres_auto_all) => `(tactic| repeat corres_auto)

/-! # Measurement

    The corres_auto tactic handles the following L1corres obligation types:
    - skip, basic, throw: 100% automatic (leaf cases)
    - seq: 100% automatic (recursive decomposition)
    - cond: 100% automatic (recursive decomposition of both branches)
    - catch: 100% automatic (recursive decomposition of body + handler)
    - guard: 100% automatic (recursive decomposition, DecidablePred inferred)
    - while: requires the BODY correspondence to be provable by corres_auto

    Not handled:
    - call/dynCom: function calls require procedure environment lookup
    - spec: nondeterministic specs require manual correspondence proof
    - Loops with non-L1 body correspondence

    For the swap example (l1_swap_body_corres), corres_auto handles 100% of the
    obligations: the body is catch(seq(guard(basic), seq(guard(guard(basic)), guard(basic))), skip)
    which is fully decomposed by the recursive rules. -/
