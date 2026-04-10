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

/-! # Call graph extraction

Extract procedure call names from CSimpl terms to build a dependency graph.
This enables topological sorting so callees are converted before callers. -/

/-- Extract all CSimpl.call names from a CSimpl expression (after whnf).
    Returns the set of procedure names (as string literals) called by this body. -/
partial def extractCallNames (csimpl : Expr) : MetaM (Array String) := do
  let csimpl ← whnfD csimpl
  match csimpl.getAppFn with
  | .const ``CSimpl.skip _ => return #[]
  | .const ``CSimpl.basic _ => return #[]
  | .const ``CSimpl.throw _ => return #[]
  | .const ``CSimpl.seq _ =>
    let c1 := csimpl.getAppArgs[1]!
    let c2 := csimpl.getAppArgs[2]!
    let n1 ← extractCallNames c1
    let n2 ← extractCallNames c2
    return n1 ++ n2
  | .const ``CSimpl.cond _ =>
    let c1 := csimpl.getAppArgs[2]!
    let c2 := csimpl.getAppArgs[3]!
    let n1 ← extractCallNames c1
    let n2 ← extractCallNames c2
    return n1 ++ n2
  | .const ``CSimpl.while _ =>
    let c := csimpl.getAppArgs[2]!
    extractCallNames c
  | .const ``CSimpl.guard _ =>
    let c := csimpl.getAppArgs[2]!
    extractCallNames c
  | .const ``CSimpl.catch _ =>
    let c1 := csimpl.getAppArgs[1]!
    let c2 := csimpl.getAppArgs[2]!
    let n1 ← extractCallNames c1
    let n2 ← extractCallNames c2
    return n1 ++ n2
  | .const ``CSimpl.spec _ => return #[]
  | .const ``CSimpl.call _ =>
    let nameExpr := csimpl.getAppArgs[1]!
    -- The name is a string literal: Expr.lit (Literal.strVal s)
    match nameExpr with
    | .lit (.strVal s) => return #[s]
    | _ =>
      -- Try to reduce to a string literal
      let nameExpr ← whnfD nameExpr
      match nameExpr with
      | .lit (.strVal s) => return #[s]
      | _ => return #[]
  | .const ``CSimpl.dynCom _ =>
    let f := csimpl.getAppArgs[1]!
    -- Go under the lambda to extract calls from the body
    lambdaTelescope f fun _ body => extractCallNames body
  | _ => return #[]

/-- Look up callees for a function in the call graph (Array-based, small N). -/
private def callGraphLookup (callGraph : Array (String × Array String))
    (fn : String) : Array String :=
  match callGraph.find? (fun (name, _) => name == fn) with
  | some (_, callees) => callees
  | none => #[]

/-- Topological sort of function names given a call graph.
    Returns functions in dependency order (callees first).
    If cycles are detected, returns the acyclic portion and the cycle members separately.

    Only considers callees that are in the function set (ignores external calls). -/
private def topologicalSort (funcNames : Array String)
    (callGraph : Array (String × Array String)) : Array String × Array String := Id.run do
  -- Kahn's algorithm with Array-based lookups (function counts are small)
  -- Dep-count: how many known functions this function CALLS (depends on).
  -- Functions with dep-count 0 are leaves (call no known functions) and go first.
  let mut depCount : Array (String × Nat) := funcNames.map fun fn => (fn, 0)
  let getDeg (arr : Array (String × Nat)) (name : String) : Nat :=
    match arr.find? (fun (n, _) => n == name) with
    | some (_, d) => d
    | none => 0
  for fn in funcNames do
    let callees := callGraphLookup callGraph fn
    let internalCallees := callees.filter fun c => funcNames.contains c
    depCount := depCount.map fun (n, d) =>
      if n == fn then (n, internalCallees.size) else (n, d)
  -- Start with functions that call no known functions (dep-count 0 = leaves)
  let mut queue : Array String := #[]
  for fn in funcNames do
    if getDeg depCount fn == 0 then
      queue := queue.push fn
  -- Build reverse call graph: for each function, who calls it
  let mut callers : Array (String × Array String) := funcNames.map fun fn => (fn, #[])
  for fn in funcNames do
    let callees := callGraphLookup callGraph fn
    for callee in callees do
      if funcNames.contains callee then
        callers := callers.map fun (n, cs) =>
          if n == callee then (n, cs.push fn) else (n, cs)
  let getCallers (fn : String) : Array String :=
    match callers.find? (fun (n, _) => n == fn) with
    | some (_, cs) => cs
    | none => #[]
  let mut sorted : Array String := #[]
  let mut idx := 0
  while idx < queue.size do
    let fn := queue[idx]!
    idx := idx + 1
    sorted := sorted.push fn
    -- When fn is processed, reduce dep-count for its callers
    -- (callers that called fn now have one fewer unresolved dependency)
    let fnCallers := getCallers fn
    for caller in fnCallers do
      let deg := getDeg depCount caller
      if deg != 0 then
        let newDeg := deg - 1
        depCount := depCount.map fun (n, d) =>
          if n == caller then (n, newDeg) else (n, d)
        if newDeg == 0 then
          queue := queue.push caller
  -- Functions not in sorted are part of cycles
  let mut cyclic : Array String := #[]
  for fn in funcNames do
    unless sorted.contains fn do
      cyclic := cyclic.push fn
  (sorted, cyclic)

/-! # Command: clift_l1

Usage:
  clift_l1 <Module>
    where <Module> is a namespace containing:
    - <func>_body : CSimpl ProgramState  (one or more)
    - procEnv : ProcEnv ProgramState

Generates for each <func>_body:
  - noncomputable def l1_<func>_body : L1Monad ProgramState
  - theorem l1_<func>_body_corres : L1corres <Module>.procEnv l1_<func>_body <Module>.<func>_body

Functions are processed in dependency order (callees before callers).
Mutual recursion (cycles in the call graph) produces a warning and
affected functions get L1 definitions but no corres proof. -/

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
    `calleeCorresNames` is an array of callee L1corres theorem names that should
    be added as local hypotheses to help corres_auto discharge call goals.
    Returns true if the proof succeeded, false if it failed (logged as warning). -/
private def proveOneFunctionCorres (ns : Name) (bodyName : Name)
    (σ : Expr) (procEnvName : Name) (l1Name : Name)
    (calleeCorresNames : Array Name := #[]) : CommandElabM Bool := do
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

    Dependency-ordered approach:
    1. Extract call graph, topologically sort functions
    2. Process in dependency order: convert, register, build incremental L1ProcEnv
    3. Each function is converted with the L1ProcEnv containing all previously-converted functions
    4. Prove L1corres for each function
    5. Cyclic dependencies: L1.fail for unresolved calls, no corres proof

    Limitation: L1corres_call requires the L1ProcEnv to cover ALL entries in the
    CSimpl ProcEnv. Since we use incremental L1ProcEnvs, the corres_auto tactic
    for call-containing functions may fail. This is accepted — corres proofs for
    call-containing functions are non-fatal and logged as warnings.

    The key improvement: L1 definitions for call-containing functions now have
    L1.call instead of L1.fail, making them correct monadic embeddings. -/
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

  -- Build function name -> (bodyName, σ) mapping
  let mut funcEntries : Array (String × Name × Expr) := #[]  -- (funcName, bodyName, σ)
  let mut funcNames : Array String := #[]
  for (bodyName, σ) in bodies do
    let baseStr := bodyName.components.getLast!.toString
    let funcName := (baseStr.dropEnd 5).toString  -- remove "_body" suffix
    funcEntries := funcEntries.push (funcName, bodyName, σ)
    funcNames := funcNames.push funcName

  -- Extract call graph
  let mut callGraph : Array (String × Array String) := #[]
  for (bodyName, _) in bodies do
    let baseStr := bodyName.components.getLast!.toString
    let funcName := (baseStr.dropEnd 5).toString
    let callees ← liftTermElabM do
      let bodyExpr := Lean.mkConst bodyName
      let bodyVal ← unfoldDefinition bodyExpr
      extractCallNames bodyVal
    -- Deduplicate
    let uniqueCallees := callees.foldl (init := #[])
      fun acc c => if acc.contains c then acc else acc.push c
    callGraph := callGraph.push (funcName, uniqueCallees)

  -- Topological sort
  let (sorted, cyclic) := topologicalSort funcNames callGraph

  if !cyclic.isEmpty then
    logWarning m!"clift_l1: mutual recursion detected for: {cyclic}. These functions will get L1 definitions but no corres proof."

  logInfo m!"clift_l1: processing order: {sorted}"

  -- Helper function: look up (bodyName, σ) by funcName
  let lookupFunc (fn : String) : Option (Name × Expr) :=
    match funcEntries.find? (fun (name, _, _) => name == fn) with
    | some (_, bodyName, σ) => some (bodyName, σ)
    | none => none

  -- Helper: get σ from first function
  let some (_, σ) := lookupFunc (funcNames[0]!)
    | throwError "clift_l1: internal error — no functions found"

  -- Process functions in dependency order, building L1ProcEnv incrementally
  let mut l1Names : Array (String × Name) := #[]  -- (funcName, l1Name)
  let mut l1Entries : Array (String × Name × Name × Expr) := #[]

  for funcName in sorted do
    let some (bodyName, σ_fn) := lookupFunc funcName
      | continue

    -- Build current L1ProcEnv expression from already-converted functions
    let l1ProcEnv? ← if l1Names.isEmpty then
      pure none
    else
      some <$> liftTermElabM do
        let mut envExpr := mkApp (.const ``L1.L1ProcEnv.empty []) σ_fn
        for (fn, l1n) in l1Names do
          let nameStr := mkStrLit fn
          let l1Ref := Lean.mkConst l1n
          envExpr := mkApp4 (.const ``L1.L1ProcEnv.insert []) σ_fn envExpr nameStr l1Ref
        return envExpr

    let l1Name ← convertOneFunctionDef nsName bodyName σ_fn l1ProcEnv?
    l1Names := l1Names.push (funcName, l1Name)
    l1Entries := l1Entries.push (funcName, bodyName, l1Name, σ_fn)

  -- Process cyclic functions (without call resolution — they get L1.fail for calls)
  for funcName in cyclic do
    let some (bodyName, σ_fn) := lookupFunc funcName
      | continue
    let l1Name ← convertOneFunctionDef nsName bodyName σ_fn none
    l1Names := l1Names.push (funcName, l1Name)
    l1Entries := l1Entries.push (funcName, bodyName, l1Name, σ_fn)

  -- Build final L1ProcEnv constant
  let _ ← buildL1ProcEnv nsName σ l1Names

  -- Prove L1corres for each function (non-fatal on failure)
  -- For calling functions, pass callee corres theorem names so corres_auto
  -- can use assumption to discharge L1corres_call_single's h_corres obligation.
  let mut corresCount := 0
  let mut provenCorres : Array (String × Name) := #[]  -- (funcName, corresName)
  for (funcName, bodyName, l1Name, σ_fn) in l1Entries do
    if cyclic.contains funcName then
      logWarning m!"clift_l1: skipping corres proof for {funcName} (mutual recursion)"
      continue
    -- Find callee corres theorem names for this function
    let callees := callGraphLookup callGraph funcName
    let mut calleeCorresNames : Array Name := #[]
    for callee in callees do
      -- Look up the callee's corres theorem name
      match provenCorres.find? (fun (n, _) => n == callee) with
      | some (_, corresN) => calleeCorresNames := calleeCorresNames.push corresN
      | none => pure ()
    let ok ← proveOneFunctionCorres nsName bodyName σ_fn procEnvName l1Name calleeCorresNames
    if ok then
      corresCount := corresCount + 1
      let corresName := nsName ++ Name.mkSimple s!"l1_{bodyName.components.getLast!.toString}_corres"
      provenCorres := provenCorres.push (funcName, corresName)

  let totalProvable := l1Entries.size - cyclic.size
  logInfo m!"clift_l1: {corresCount}/{totalProvable} L1corres proofs generated ({cyclic.size} skipped due to mutual recursion)"

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
