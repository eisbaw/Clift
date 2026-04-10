-- Pipeline: Unified 'clift' command chaining L1 -> L2 -> L3
--
-- `clift <Module>` runs the entire automated pipeline:
--   1. clift_l1: CSimpl -> L1 monadic form + L1corres proof
--   2. clift_l2: L1 -> L2 local extraction + L2corres_fwd proof
--   3. clift_l3: L2 -> classify monad level (pure/nondet) + L1Deterministic proof
--
-- L5 (WordAbstract) requires user-provided Nat definitions and is
-- invoked separately via `clift_wa`.
--
-- This is the Lean 4 equivalent of AutoCorres2's `autocorres` command.
--
-- Reference: ext/AutoCorres2/autocorres.ML

import Clift.Lifting.L1Auto
import Clift.Lifting.L2Auto
import Clift.Lifting.L3Auto
import Clift.Lifting.L5Auto
import Lean

open Lean Meta Elab Command

/-! # clift: one-shot pipeline command -/

/-- `clift <Module>` runs the full lifting pipeline on a Generated module.

    Requires:
    - `<Module>.procEnv` exists
    - One or more `<Module>.*_body : CSimpl ProgramState` definitions

    Generates for each function:
    - `<Module>.l1_<fn>_body` — L1 monadic form
    - `<Module>.l1_<fn>_body_corres` — L1corres proof
    - `<Module>.l2_<fn>_body` — L2 wrapper (locals extracted)
    - `<Module>.l2_<fn>_body_corres_fwd` — L2 forward correspondence
    - `<Module>.l3_<fn>_body_level` — MonadLevel classification
    - `<Module>.l3_<fn>_body_det` — L1Deterministic proof (pure only)

    Example:
      clift Gcd
      -- Now available: Gcd.l1_gcd_body, Gcd.l2_gcd_body, Gcd.l3_gcd_body_level
-/
elab "clift " ns:ident : command => do
  let nsName := ns.getId
  logInfo m!"clift: starting pipeline for {nsName}"

  -- Stage 1: L1
  logInfo m!"clift: === Stage 1: SimplConv (CSimpl -> L1) ==="
  elabCommand (← `(command| clift_l1 $(mkIdent nsName)))

  -- Stage 2: L2
  logInfo m!"clift: === Stage 2: LocalVarExtract (L1 -> L2) ==="
  elabCommand (← `(command| clift_l2 $(mkIdent nsName)))

  -- Stage 3: L3 classification
  logInfo m!"clift: === Stage 3: TypeStrengthen (classify monad levels) ==="
  elabCommand (← `(command| clift_l3 $(mkIdent nsName)))

  logInfo m!"clift: pipeline complete for {nsName}"
