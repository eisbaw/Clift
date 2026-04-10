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
--   CSimpl.call n     -> L1.fail  (placeholder: real call support is Phase B)
--   CSimpl.dynCom f   -> L1.fail  (placeholder: real dynCom support is Phase B)
--
-- Reference: ext/AutoCorres2/simpl_conv.ML
-- Reference: Clift/Tactics/CorresAuto.lean (proof automation)

import Clift.Lifting.SimplConv
import Clift.Tactics.CorresAuto
import Lean

open Lean Meta Elab Command Term Tactic

/-! # Core MetaM: convert CSimpl expression to L1 monadic expression -/

/-- Convert a CSimpl expression to its L1 monadic equivalent.
    Takes the state type σ (as an Expr) and a CSimpl σ expression.
    Returns an L1Monad σ expression.

    The conversion is purely structural — each CSimpl constructor maps to
    exactly one L1 combinator (or a pair for guard -> seq + guard).

    Assumptions:
    - Input expression is in whnf with respect to CSimpl constructors
    - State type σ is consistent throughout the term
    - Guard predicates have DecidablePred instances (required by L1.guard)

    Limitations:
    - CSimpl.call and CSimpl.dynCom produce L1.fail (not yet supported)
    - No optimization (e.g., skip elimination, guard merging)
    - Does not handle CSimpl terms that require further unfolding -/
partial def csimplToL1 (σ : Expr) (csimpl : Expr) : MetaM Expr := do
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
    let l1 ← csimplToL1 σ c1
    let r1 ← csimplToL1 σ c2
    return mkApp3 (.const ``L1.seq []) σ l1 r1
  | .const ``CSimpl.cond _ =>
    let b := csimpl.getAppArgs[1]!
    let c1 := csimpl.getAppArgs[2]!
    let c2 := csimpl.getAppArgs[3]!
    let l1 ← csimplToL1 σ c1
    let r1 ← csimplToL1 σ c2
    return mkApp4 (.const ``L1.condition []) σ b l1 r1
  | .const ``CSimpl.while _ =>
    let b := csimpl.getAppArgs[1]!
    let c := csimpl.getAppArgs[2]!
    let lc ← csimplToL1 σ c
    return mkApp3 (.const ``L1.while []) σ b lc
  | .const ``CSimpl.guard _ =>
    let p := csimpl.getAppArgs[1]!
    let c := csimpl.getAppArgs[2]!
    let lc ← csimplToL1 σ c
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
    let l1 ← csimplToL1 σ c1
    let r1 ← csimplToL1 σ c2
    return mkApp3 (.const ``L1.catch []) σ l1 r1
  | .const ``CSimpl.spec _ =>
    let r := csimpl.getAppArgs[1]!
    return mkApp2 (.const ``L1.spec []) σ r
  | .const ``CSimpl.call _ =>
    logWarning m!"csimplToL1: CSimpl.call not yet supported, emitting L1.fail"
    return mkApp (.const ``L1.fail []) σ
  | .const ``CSimpl.dynCom _ =>
    logWarning m!"csimplToL1: CSimpl.dynCom not yet supported, emitting L1.fail"
    return mkApp (.const ``L1.fail []) σ
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
    Adds the L1 definition and L1corres theorem to the environment. -/
private def convertOneFunction (ns : Name) (bodyName : Name)
    (σ : Expr) (procEnvName : Name) : CommandElabM Unit := do
  -- Derive names: Gcd.gcd_body -> l1_gcd_body, l1_gcd_body_corres
  let baseStr := bodyName.components.getLast!.toString
  let l1Name := ns ++ Name.mkSimple s!"l1_{baseStr}"
  let corresName := ns ++ Name.mkSimple s!"l1_{baseStr}_corres"

  -- Step 1: Build the L1 term from the CSimpl body
  liftTermElabM do
    let bodyExpr := Lean.mkConst bodyName
    -- Delta-reduce to get the actual CSimpl constructor tree
    let bodyVal ← unfoldDefinition bodyExpr

    let l1Expr ← csimplToL1 σ bodyVal

    -- Build the type: L1Monad σ = NondetM σ (Except Unit Unit)
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

  -- Step 2: Prove L1corres by tactic
  liftTermElabM do
    let l1Ref := Lean.mkConst l1Name
    let bodyRef := Lean.mkConst bodyName
    let procEnvRef := Lean.mkConst procEnvName
    let corresType := mkApp4 (.const ``L1corres []) σ procEnvRef l1Ref bodyRef

    -- Create mvar and prove via tactics
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

/-- `clift_l1 <Module>` command: auto-convert all CSimpl bodies in <Module> to L1 form. -/
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

  for (bodyName, σ) in bodies do
    convertOneFunction nsName bodyName σ procEnvName

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
  convertOneFunction ns bodyName σ procEnvName
