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
--   .dynCom f  -> L1corres_dynCom
--   .call n    -> L1corres_call_single (with callee corres from hypotheses or env)
--
-- Usage:
--   `corres_auto` — recursively decompose the entire L1corres goal
--
-- Reference: l1_swap_body_corres in SwapProof.lean shows the manual version.

import Clift.Lifting.SimplConv
import Lean

open Lean Meta Elab Tactic Term

/-! # corres_auto MetaM tactic

A proper MetaM tactic that can inspect goal state and look up callee corres
theorems by name convention. This replaces the previous macro-based approach
which couldn't handle calls because macros can't inspect goals. -/

/-- Check if an expression is an L1corres application (possibly with implicit args).
    Returns (σ, Γ, m, c) if it matches L1corres {σ} Γ m c. -/
private def matchL1corres (e : Expr) : MetaM (Option (Expr × Expr × Expr × Expr)) := do
  -- Don't whnf — L1corres is a def, whnf would unfold it
  -- Check if the expression has L1corres as the function head
  if e.isAppOf ``L1corres then
    let args := e.getAppArgs
    if args.size >= 4 then
      -- σ is first implicit, Γ m c are the last three
      let n := args.size
      return some (args[0]!, args[n-3]!, args[n-2]!, args[n-1]!)
    else
      return none
  else
    return none

/-- Extract the CSimpl constructor head from the third argument of L1corres.
    Returns the constructor name if the goal is `L1corres Γ m c` and `c`
    has a recognizable CSimpl constructor. -/
private def getCSimplHead (goal : MVarId) : MetaM (Option Name) := do
  let target ← goal.getType
  let some (_, _, _, csimpl) ← matchL1corres target | return none
  let csimpl ← whnfD csimpl
  match csimpl.getAppFn with
  | .const n _ => return some n
  | _ => return none

/-- Try to find a callee name from a CSimpl.call term.
    Extracts the string literal from .call "name". -/
private def getCallName (goal : MVarId) : MetaM (Option String) := do
  let target ← goal.getType
  let some (_, _, _, csimpl) ← matchL1corres target | return none
  let csimpl ← whnfD csimpl
  unless csimpl.isAppOf ``CSimpl.call do return none
  let nameExpr := csimpl.getAppArgs[1]!
  let nameExpr ← whnfD nameExpr
  match nameExpr with
  | .lit (.strVal s) => return some s
  | _ => return none

/-- Try to find an L1corres proof for the callee.
    Searches the environment for any declaration named `*.l1_<callee>_body_corres`
    whose type is `L1corres`. Also checks local hypotheses. -/
private def findCalleeCorres (goal : MVarId) (calleeName : String) : MetaM (Option Expr) := do
  -- Search local context for any L1corres hypothesis
  let lctx ← goal.getDecl >>= fun d => pure d.lctx
  for decl in lctx do
    if decl.isAuxDecl then continue
    let declType := decl.type
    if declType.isAppOf ``L1corres then
      return some decl.toExpr
  -- Search environment by naming convention.
  -- The callee corres theorem should be in the same namespace as procEnv.
  let target ← instantiateMVars (← goal.getType)
  let some (_, gamma, _, _) ← matchL1corres target | do
    return none
  -- Gamma might be an unresolved metavar — try to instantiate
  let gamma ← instantiateMVars gamma
  -- gamma should be a const reference to procEnv (don't whnf — that unfolds it to a lambda)
  let gammaConst ← do
    match gamma.getAppFn with
    | .const name _ => pure (some name)
    | _ => pure none
  match gammaConst with
  | some name =>
    let ns := name.getPrefix
    let corresName := ns ++ Name.mkSimple s!"l1_{calleeName}_body_corres"
    let env ← getEnv
    if env.contains corresName then
      return some (mkConst corresName)
    -- Also try without l1_ prefix variations
    let corresName2 := ns ++ (Name.mkSimple s!"l1_{calleeName}_body") ++ `corres
    if env.contains corresName2 then
      return some (mkConst corresName2)
    return none
  | none =>
    -- Try brute force: search env for any `l1_<callee>_body_corres`
    let env ← getEnv
    let targetSuffix := s!"l1_{calleeName}_body_corres"
    for (name, _) in env.constants.map₁.toList do
      if name.toString.endsWith targetSuffix then
        return some (mkConst name)
    return none

/-- Try to close a non-L1corres goal using rfl, simp, or native_decide.
    Returns true if the goal was closed. -/
private def tryCloseGoal (g : MVarId) : TacticM Bool := do
  -- Try rfl first
  try
    let _ ← Tactic.run g do
      evalTactic (← `(tactic| rfl))
    return true
  catch _ => pure ()
  -- Try simp with insert/empty
  try
    let _ ← Tactic.run g do
      evalTactic (← `(tactic|
        simp (config := { decide := true })
          [ProcEnv.insert, ProcEnv.empty,
           L1.L1ProcEnv.insert, L1.L1ProcEnv.empty]))
    return true
  catch _ => pure ()
  -- Try native_decide
  try
    let _ ← Tactic.run g do
      evalTactic (← `(tactic| native_decide))
    return true
  catch _ => pure ()
  return false

/-- The core recursive corres_auto implementation.
    Dispatches on the CSimpl constructor and applies the matching lemma. -/
partial def corresAutoCore (goal : MVarId) : TacticM (List MVarId) := do
  let some head ← getCSimplHead goal | do
    let target ← goal.getType
    let nargs := target.getAppNumArgs
    let isApp := target.isAppOf ``L1corres
    let headStr := toString (← ppExpr target.getAppFn)
    throwTacticEx `corres_auto goal
      m!"not an L1corres goal (nargs={nargs} isApp={isApp} headStr={headStr} ctor={target.ctorName})"
  match head with
  | ``CSimpl.skip =>
    let gs ← goal.apply (mkConst ``L1corres_skip)
    return gs
  | ``CSimpl.basic =>
    let gs ← goal.apply (mkConst ``L1corres_basic)
    return gs
  | ``CSimpl.throw =>
    let gs ← goal.apply (mkConst ``L1corres_throw)
    return gs
  | ``CSimpl.seq =>
    let gs ← goal.apply (mkConst ``L1corres_seq)
    let mut remaining := []
    for g in gs do
      let gs' ← corresAutoCore g
      remaining := remaining ++ gs'
    return remaining
  | ``CSimpl.cond =>
    let gs ← goal.apply (mkConst ``L1corres_cond)
    let mut remaining := []
    for g in gs do
      let gs' ← corresAutoCore g
      remaining := remaining ++ gs'
    return remaining
  | ``CSimpl.catch =>
    let gs ← goal.apply (mkConst ``L1corres_catch)
    let mut remaining := []
    for g in gs do
      let gs' ← corresAutoCore g
      remaining := remaining ++ gs'
    return remaining
  | ``CSimpl.guard =>
    let gs ← goal.apply (mkConst ``L1corres_guard)
    let mut remaining := []
    for g in gs do
      let gs' ← corresAutoCore g
      remaining := remaining ++ gs'
    return remaining
  | ``CSimpl.while =>
    let gs ← goal.apply (mkConst ``L1corres_while)
    let mut remaining := []
    for g in gs do
      let gs' ← corresAutoCore g
      remaining := remaining ++ gs'
    return remaining
  | ``CSimpl.dynCom =>
    let gs ← goal.apply (mkConst ``L1corres_dynCom)
    let mut remaining := []
    for g in gs do
      -- dynCom introduces a forall, intro it
      let (_, g') ← g.intro `s_dyncom
      let gs' ← corresAutoCore g'
      remaining := remaining ++ gs'
    return remaining
  | ``CSimpl.call =>
    -- Try L1corres_call first (for complete L1ProcEnvs)
    try
      let gs ← goal.apply (mkConst ``L1corres_call)
      -- Need to close h_env and h_none subgoals
      let mut remaining := []
      for g in gs do
        let gs' ← Tactic.run g do
          evalTactic (← `(tactic| intro; intro; intro; simp; constructor <;> rfl))
        remaining := remaining ++ gs'
      return remaining
    catch _ =>
      -- Try L1corres_call_single with hypothesis lookup
      let some calleeName ← getCallName goal
        | throwTacticEx `corres_auto goal "CSimpl.call: could not extract callee name"
      -- Find callee L1corres proof in hypotheses or environment
      let some calleeProof ← findCalleeCorres goal calleeName | do
        -- Debug: show what we know about the goal
        let target ← goal.getType
        let some (_, gamma, _, _) ← matchL1corres target | do
          throwTacticEx `corres_auto goal
            s!"CSimpl.call \"{calleeName}\": goal not L1corres"
        let gammaWhnf ← whnfD gamma
        let gammaFn := gammaWhnf.getAppFn
        let gammaKind := gammaFn.ctorName
        let gammaName := match gammaFn with
          | .const n _ => toString n
          | .fvar id => toString id.name
          | _ => "other"
        throwTacticEx `corres_auto goal
          m!"CSimpl.call \"{calleeName}\": no corres found (Γ kind={gammaKind} name={gammaName})"
      let gs ← goal.apply (mkConst ``L1corres_call_single)
      -- gs should have subgoals for: body, l1_body, h_gamma, h_l1gamma, h_corres
      -- Process non-L1corres goals first (so body/l1_body get assigned),
      -- then close the L1corres goal with the callee proof.
      let mut remaining := []
      let mut l1corresGoals := []
      for g in gs do
        let target ← instantiateMVars (← g.getType)
        if target.isAppOf ``L1corres then
          l1corresGoals := l1corresGoals ++ [g]
        else
          -- Try to close with various tactics
          let closed ← tryCloseGoal g
          if !closed then remaining := remaining ++ [g]
      -- Now close L1corres goals with callee proof
      for g in l1corresGoals do
        -- Re-check if it's still open (mvar might have been assigned by earlier unification)
        let g_type ← instantiateMVars (← g.getType)
        if g_type.hasMVar then
          remaining := remaining ++ [g]
        else
          try
            let gs' ← g.apply calleeProof
            remaining := remaining ++ gs'
          catch _ =>
            remaining := remaining ++ [g]
      return remaining
  | _ =>
    throwTacticEx `corres_auto goal s!"unrecognized CSimpl constructor: {head}"

/-- `corres_auto` tactic: recursively decompose an L1corres goal. -/
elab "corres_auto" : tactic => do
  let goal ← getMainGoal
  let remaining ← corresAutoCore goal
  replaceMainGoal remaining

/-- `corres_auto_all` tactic: same as corres_auto (already recursive). -/
syntax "corres_auto_all" : tactic
macro_rules
  | `(tactic| corres_auto_all) => `(tactic| corres_auto)

/-! # Measurement

    The corres_auto tactic handles the following L1corres obligation types:
    - skip, basic, throw: 100% automatic (leaf cases)
    - seq: 100% automatic (recursive decomposition)
    - cond: 100% automatic (recursive decomposition of both branches)
    - catch: 100% automatic (recursive decomposition of body + handler)
    - guard: 100% automatic (recursive decomposition, DecidablePred inferred)
    - while: requires the BODY correspondence to be provable by corres_auto
    - call: automatic when callee L1corres is available as hypothesis
    - dynCom: automatic (introduces state variable and recurses)

    For call-containing functions, the caller must provide callee L1corres
    theorems as local hypotheses (via `have`). The tactic finds them by
    searching the local context for L1corres terms. -/
