-- L1Auto: MetaM automation for CSimpl -> L1 monadic conversion
--
-- Given a CSimpl function body definition, automatically generate:
-- 1. The L1 monadic equivalent (noncomputable def l1_<name> : L1Monad σ)
-- 2. The L1corres proof (theorem l1_<name>_corres : L1corres Γ l1_<name> <csimpl>)
--
-- The conversion is a direct structural recursion over CSimpl constructors,
-- mirroring AutoCorres2's simpl_conv.ML but implemented in Lean 4 MetaM.
--
-- Constructor mapping:
--   CSimpl.skip       -> L1.skip
--   CSimpl.basic f    -> L1.modify f
--   CSimpl.seq c1 c2  -> L1.seq (convert c1) (convert c2)
--   CSimpl.cond b t e -> L1.condition b (convert t) (convert e)
--   CSimpl.while b c  -> L1.while b (convert c)
--   CSimpl.guard p c  -> L1.seq (L1.guard p) (convert c)
--   CSimpl.throw      -> L1.throw
--   CSimpl.catch c h  -> L1.catch (convert c) (convert h)
--   CSimpl.spec r     -> L1.spec r
--   CSimpl.call n     -> L1.call l1Γ n  (with L1ProcEnv)
--   CSimpl.dynCom f   -> L1.dynCom (fun s => convert (f s))
--
-- Reference: ext/AutoCorres2/simpl_conv.ML
-- Reference: Clift/Tactics/CorresAuto.lean (proof automation)

import Clift.Lifting.SimplConv
import Clift.Tactics.CorresAuto
import Lean

open Lean Meta Elab Command Term Tactic

/-! # Core MetaM: convert CSimpl expression to L1 monadic expression -/

/-- Convert a CSimpl expression to its L1 monadic equivalent.
    Takes the state type σ (as an Expr), an optional L1ProcEnv expression
    (for resolving calls), and a CSimpl σ expression.
    Returns an L1Monad σ expression.

    The conversion is purely structural — each CSimpl constructor maps to
    exactly one L1 combinator (or a pair for guard -> seq + guard).

    Assumptions:
    - Input expression is in whnf with respect to CSimpl constructors
    - State type σ is consistent throughout the term
    - Guard predicates have DecidablePred instances (required by L1.guard)

    Limitations:
    - No optimization (e.g., skip elimination, guard merging)
    - Does not handle CSimpl terms that require further unfolding -/
partial def csimplToL1 (σ : Expr) (csimpl : Expr)
    (l1ProcEnv? : Option Expr := none) : MetaM Expr := do
  let csimpl ← whnfD csimpl
  match csimpl.getAppFn with
  | .const ``CSimpl.skip _ =>
    return mkApp (.const ``L1.skip []) σ
  | .const ``CSimpl.basic _ =>
    let f := csimpl.getAppArgs[1]!
    return mkApp2 (.const ``L1.modify []) σ f
  | .const ``CSimpl.seq _ =>
    let c1 := csimpl.getAppArgs[1]!
    let c2 := csimpl.getAppArgs[2]!
    let l1 ← csimplToL1 σ c1 l1ProcEnv?
    let r1 ← csimplToL1 σ c2 l1ProcEnv?
    return mkApp3 (.const ``L1.seq []) σ l1 r1
  | .const ``CSimpl.cond _ =>
    let b := csimpl.getAppArgs[1]!
    let c1 := csimpl.getAppArgs[2]!
    let c2 := csimpl.getAppArgs[3]!
    let l1 ← csimplToL1 σ c1 l1ProcEnv?
    let r1 ← csimplToL1 σ c2 l1ProcEnv?
    return mkApp4 (.const ``L1.condition []) σ b l1 r1
  | .const ``CSimpl.while _ =>
    let b := csimpl.getAppArgs[1]!
    let c := csimpl.getAppArgs[2]!
    let lc ← csimplToL1 σ c l1ProcEnv?
    return mkApp3 (.const ``L1.while []) σ b lc
  | .const ``CSimpl.guard _ =>
    let p := csimpl.getAppArgs[1]!
    let c := csimpl.getAppArgs[2]!
    let lc ← csimplToL1 σ c l1ProcEnv?
    -- guard p c -> L1.seq (L1.guard p) (convert c)
    -- L1.guard needs [DecidablePred p] — synthesize it
    let dpType := mkApp2 (.const ``DecidablePred [.zero]) σ p
    let inst ← synthInstance dpType
    let guardExpr := mkApp3 (.const ``L1.guard []) σ p inst
    return mkApp3 (.const ``L1.seq []) σ guardExpr lc
  | .const ``CSimpl.throw _ =>
    return mkApp (.const ``L1.throw []) σ
  | .const ``CSimpl.catch _ =>
    let c1 := csimpl.getAppArgs[1]!
    let c2 := csimpl.getAppArgs[2]!
    let l1 ← csimplToL1 σ c1 l1ProcEnv?
    let r1 ← csimplToL1 σ c2 l1ProcEnv?
    return mkApp3 (.const ``L1.catch []) σ l1 r1
  | .const ``CSimpl.spec _ =>
    let r := csimpl.getAppArgs[1]!
    return mkApp2 (.const ``L1.spec []) σ r
  | .const ``CSimpl.call _ =>
    let name := csimpl.getAppArgs[1]!
    match l1ProcEnv? with
    | some l1Γ =>
      -- L1.call l1Γ name
      return mkApp3 (.const ``L1.call []) σ l1Γ name
    | none =>
      logWarning m!"csimplToL1: CSimpl.call encountered but no L1ProcEnv provided, emitting L1.fail"
      return mkApp (.const ``L1.fail []) σ
  | .const ``CSimpl.dynCom _ =>
    let f := csimpl.getAppArgs[1]!
    -- f : σ → CSimpl σ, we need to produce (fun s => csimplToL1 (f s))
    -- Use lambdaTelescope to go under the lambda
    match l1ProcEnv? with
    | some l1Γ =>
      let l1_f ← lambdaTelescope f fun xs body => do
        let l1_body ← csimplToL1 σ body (some l1Γ)
        mkLambdaFVars xs l1_body
      return mkApp2 (.const ``L1.dynCom []) σ l1_f
    | none =>
      -- Without L1ProcEnv, try converting the dynCom body anyway
      let l1_f ← lambdaTelescope f fun xs body => do
        let l1_body ← csimplToL1 σ body none
        mkLambdaFVars xs l1_body
      return mkApp2 (.const ``L1.dynCom []) σ l1_f
  | other =>
    throwError "csimplToL1: unexpected CSimpl head: {other}\nFull term: {csimpl}"

/-! # Command: clift_l1

Usage:
  clift_l1 <Module>
    where <Module> is a namespace containing:
    - <func>_body : CSimpl ProgramState  (one or more)
    - procEnv : ProcEnv ProgramState

Generates for each <func>_body:
  - noncomputable def l1_<func>_body : L1Monad ProgramState
  - theorem l1_<func>_body_corres : L1corres <Module>.procEnv l1_<func>_body <Module>.<func>_body
-/

/-- Find all `*_body` definitions in a namespace that have type `CSimpl σ` for some σ. -/
private def findCSimplBodies (ns : Name) : MetaM (Array (Name × Expr)) := do
  let env ← getEnv
  let mut results : Array (Name × Expr) := #[]
  for (name, info) in env.constants.map₁.toList do
    if name.getPrefix == ns && name.toString.endsWith "_body" then
      let ty ← whnfD info.type
      if ty.isAppOf ``CSimpl then
        let σ := ty.getAppArgs[0]!
        results := results.push (name, σ)
  return results

/-- Convert a single CSimpl function body to L1 form.
    Adds the L1 definition to the environment.
    Returns the L1 definition name. -/
private def convertOneFunctionDef (ns : Name) (bodyName : Name)
    (σ : Expr) (l1ProcEnv? : Option Expr) : CommandElabM Name := do
  let baseStr := bodyName.components.getLast!.toString
  let l1Name := ns ++ Name.mkSimple s!"l1_{baseStr}"

  liftTermElabM do
    let bodyExpr := Lean.mkConst bodyName
    let bodyVal ← unfoldDefinition bodyExpr
    let l1Expr ← csimplToL1 σ bodyVal l1ProcEnv?

    let exceptType := mkApp2 (.const ``Except [.zero, .zero]) (.const ``Unit []) (.const ``Unit [])
    let l1Type := mkApp2 (.const ``NondetM []) σ exceptType

    let l1Expr ← instantiateMVars l1Expr
    check l1Expr

    addDecl <| Declaration.defnDecl {
      name := l1Name
      levelParams := []
      type := l1Type
      value := l1Expr
      hints := .abbrev
      safety := .safe
    }

  return l1Name

/-- Prove L1corres for a single function (after L1 definitions exist).
    Returns true if the proof succeeded, false if it failed (logged as warning). -/
private def proveOneFunctionCorres (ns : Name) (bodyName : Name)
    (σ : Expr) (procEnvName : Name) (l1Name : Name) : CommandElabM Bool := do
  let corresName := ns ++ Name.mkSimple s!"l1_{bodyName.components.getLast!.toString}_corres"

  try
    liftTermElabM do
      let l1Ref := Lean.mkConst l1Name
      let bodyRef := Lean.mkConst bodyName
      let procEnvRef := Lean.mkConst procEnvName
      let corresType := mkApp4 (.const ``L1corres []) σ procEnvRef l1Ref bodyRef

      let proof ← mkFreshExprMVar corresType
      let mvarId := proof.mvarId!

      let goals ← Tactic.run mvarId do
        evalTactic (← `(tactic| unfold $(mkIdent l1Name) $(mkIdent bodyName)))
        evalTactic (← `(tactic| corres_auto))

      unless goals.isEmpty do
        throwError "clift_l1: corres_auto left {goals.length} unsolved goals for {bodyName}"

      let proofVal ← instantiateMVars proof

      addDecl <| Declaration.thmDecl {
        name := corresName
        levelParams := []
        type := corresType
        value := proofVal
      }

    logInfo m!"clift_l1: {bodyName} -> {l1Name} + {corresName}"
    return true
  catch e =>
    logWarning m!"clift_l1: corres proof failed for {bodyName}: {e.toMessageData} (L1 definition still available)"
    return false

/-- Build and add an L1ProcEnv definition for the module.
    Maps function names to their L1 bodies using L1ProcEnv.insert chains.
    Returns the name of the l1ProcEnv definition. -/
private def buildL1ProcEnv (ns : Name) (σ : Expr)
    (entries : Array (String × Name)) : CommandElabM Name := do
  let l1ProcEnvName := ns ++ `l1ProcEnv

  liftTermElabM do
    -- Build: L1ProcEnv.insert (L1ProcEnv.insert L1ProcEnv.empty "f1" l1_f1) "f2" l1_f2
    let mut envExpr := mkApp (.const ``L1.L1ProcEnv.empty []) σ
    for (funcName, l1BodyName) in entries do
      let nameStr := mkStrLit funcName
      let l1Ref := Lean.mkConst l1BodyName
      envExpr := mkApp4 (.const ``L1.L1ProcEnv.insert []) σ envExpr nameStr l1Ref

    let l1ProcEnvType := mkApp (.const ``L1.L1ProcEnv []) σ

    envExpr ← instantiateMVars envExpr
    check envExpr

    addDecl <| Declaration.defnDecl {
      name := l1ProcEnvName
      levelParams := []
      type := l1ProcEnvType
      value := envExpr
      hints := .abbrev
      safety := .safe
    }

  return l1ProcEnvName

/-- `clift_l1 <Module>` command: auto-convert all CSimpl bodies in <Module> to L1 form.

    Two-pass approach:
    1. Convert all function bodies (without call resolution) and add definitions
    2. Build L1ProcEnv from the converted definitions
    3. Prove L1corres for each function -/
elab "clift_l1 " ns:ident : command => do
  let nsName := ns.getId
  let bodies ← liftTermElabM <| findCSimplBodies nsName
  if bodies.isEmpty then
    throwError "clift_l1: no *_body : CSimpl definitions found in namespace {nsName}"

  let procEnvName := nsName ++ `procEnv
  let env ← getEnv
  unless env.contains procEnvName do
    throwError "clift_l1: {procEnvName} not found"

  logInfo m!"clift_l1: found {bodies.size} CSimpl bodies in {nsName}"

  -- Pass 1: Convert all bodies to L1 definitions (no call resolution yet)
  let mut l1Entries : Array (String × Name × Name × Expr) := #[]  -- (funcName, bodyName, l1Name, σ)
  for (bodyName, σ) in bodies do
    let l1Name ← convertOneFunctionDef nsName bodyName σ none
    -- Extract function name from body name (e.g., "gcd_body" -> "gcd")
    let baseStr := bodyName.components.getLast!.toString
    let funcName := (baseStr.dropEnd 5).toString  -- remove "_body" suffix
    l1Entries := l1Entries.push (funcName, bodyName, l1Name, σ)

  -- Build L1ProcEnv
  let envEntries := l1Entries.map fun (fn, _, l1n, _) => (fn, l1n)
  if let some (_, _, _, σ) := l1Entries[0]? then
    let _ ← buildL1ProcEnv nsName σ envEntries

  -- Pass 2: Prove L1corres for each function (non-fatal on failure)
  let mut corresCount := 0
  for (_, bodyName, l1Name, σ) in l1Entries do
    let ok ← proveOneFunctionCorres nsName bodyName σ procEnvName l1Name
    if ok then corresCount := corresCount + 1

  logInfo m!"clift_l1: {corresCount}/{l1Entries.size} L1corres proofs generated"

/-- `clift_l1_fn <body_name> <procEnv_name>` command: convert a single CSimpl function. -/
elab "clift_l1_fn" body:ident procEnv:ident : command => do
  let bodyName := body.getId
  let procEnvName := procEnv.getId
  let env ← getEnv
  let some info := env.find? bodyName
    | throwError "clift_l1_fn: {bodyName} not found"
  let ty ← liftTermElabM <| whnfD info.type
  unless ty.isAppOf ``CSimpl do
    throwError "clift_l1_fn: {bodyName} has type {ty}, expected CSimpl σ"
  let σ := ty.getAppArgs[0]!
  let ns := bodyName.getPrefix
  let l1Name ← convertOneFunctionDef ns bodyName σ none
  let _ ← proveOneFunctionCorres ns bodyName σ procEnvName l1Name
