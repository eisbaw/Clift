-- L1 VCG: verification condition generator for L1 monadic computations
--
-- Automates the SwapProof pattern: for a `validHoare P l1_body Q` goal,
-- decompose the L1 body into individual steps and discharge each step
-- using L1 Hoare rules with projection simp lemmas.
--
-- The key technique (from SwapProof.lean):
-- 1. Unfold the L1 body to expose L1.catch/seq/guard/modify structure
-- 2. For each guard+modify step, apply L1_guard_modify_result
-- 3. Chain steps with L1_seq_singleton_ok
-- 4. Wrap with L1_catch_singleton_ok
-- 5. Use simp with projection lemmas to keep state simple
--
-- The tactic produces bounded-depth proof terms regardless of program length.

import Clift.Lifting.FuncSpec

open Lean Meta Elab Tactic

/-! # l1_vcg tactic

The tactic decomposes `validHoare P body Q` goals for L1 monadic programs.
It applies L1 Hoare rules compositionally:

- `L1.catch body skip` -> `L1_hoare_catch_ok` (when body produces only ok results)
- `L1.seq m₁ m₂` -> `L1_hoare_seq_ok` (when m₁ produces only ok results)
- `L1.guard p` -> `L1_hoare_guard'`
- `L1.modify f` -> `L1_hoare_modify'`
- `L1.skip` -> `L1_hoare_skip`

After decomposition, leaf goals are of the form `P s → Q s` which can
be closed with intro + simp or user-provided lemmas.

Usage:
  `l1_vcg` — apply one decomposition step
  `l1_vcg_all` — repeatedly decompose until stuck
  `l1_vcg_finish [lemmas]` — decompose and try to close all goals with simp

The key improvement over `c_vcg`: works with any L1 body structure,
not just the specific patterns hardcoded in c_vcg_leaf. -/

/-- `l1_vcg` tactic: apply one L1 Hoare rule step.

    Tries rules in order. Compound rules (seq, catch) produce sub-goals
    for each component. Leaf rules (skip, guard, modify) close the goal. -/
syntax "l1_vcg" : tactic

macro_rules
  | `(tactic| l1_vcg) => `(tactic|
    first
    | apply L1_hoare_skip
    | apply L1_hoare_guard'
    | apply L1_hoare_modify'
    | apply L1_hoare_catch_ok
    | apply L1_hoare_catch
    | apply L1_hoare_seq_ok
    | apply L1_hoare_seq
    | fail "l1_vcg: no applicable L1 Hoare rule"
    )

/-- `l1_vcg_all` tactic: repeatedly apply l1_vcg to decompose the L1 program.
    Stops when no more rules apply. -/
syntax "l1_vcg_all" : tactic

macro_rules
  | `(tactic| l1_vcg_all) => `(tactic| repeat l1_vcg)

/-- `l1_vcg_simp` tactic: try to close a leaf goal from l1_vcg decomposition
    using intro + simp. Handles the common pattern where the precondition
    implies the intermediate condition after a guard/modify step. -/
syntax "l1_vcg_simp" : tactic

macro_rules
  | `(tactic| l1_vcg_simp) => `(tactic|
    first
    | (intro s hs; exact hs)
    | (intro s hs; obtain ⟨h1, h2⟩ := hs; exact ⟨h1, h2⟩)
    | (intro s hs; simp_all)
    | assumption
    | constructor <;> assumption
    )

/-- `l1_vcg_finish` tactic: apply l1_vcg_all then try l1_vcg_simp on all goals. -/
syntax "l1_vcg_finish" : tactic

macro_rules
  | `(tactic| l1_vcg_finish) => `(tactic|
    l1_vcg_all <;> try l1_vcg_simp)
