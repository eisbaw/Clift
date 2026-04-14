-- Clift/Lint/SemanticLint.lean: Semantic proof quality checks via Lean MetaM
--
-- These checks require the Lean kernel and type system -- grep/Python cannot do them.
-- Each check is a MetaM function: Name -> MetaM (Option MessageData)
-- returning Some msg if the declaration fails the check, None if it passes.
--
-- Checks implemented:
--   1. axiomAudit       — flag sorryAx or trustCompiler in transitive axiom deps
--   2. specStrength     — flag FuncSpec postconditions that don't constrain ret__val
--   3. satisfiedByTarget — flag satisfiedBy proofs not targeting Generated.* L1 bodies
--   4. tautologicalPost  — flag FuncSpec where post is definitionally True
--   5. vacuousPre        — flag FuncSpec where pre is unsatisfiable
--
-- Usage: import this module and run `#clift_lint` after importing your Examples.
--
-- We do NOT depend on Batteries -- these are standalone MetaM checks.

import Lean
import Clift.Lifting.FuncSpec

open Lean Meta Elab Command

namespace Clift.Lint

/-! # Utility -/

/-- Check if `haystack` contains `needle` as a substring. -/
private def strContains (haystack : String) (needle : String) : Bool :=
  haystack.find needle != haystack.endPos

/-- Check if a ConstantInfo is a theorem. -/
private def isThm (ci : ConstantInfo) : Bool :=
  ci matches ConstantInfo.thmInfo _

/-- Try to extract FuncSpec.mk fields (σ, pre, post) from an expression.
    Avoids full whnf which can blow up on large ProgramState types.
    Returns (pre, post) if the expression is a FuncSpec.mk application. -/
private def extractFuncSpecFields (val : Expr) : MetaM (Option (Expr × Expr)) := do
  -- First try: is it already FuncSpec.mk?
  let check (e : Expr) : Option (Expr × Expr) :=
    if e.getAppFn.isConstOf ``FuncSpec.mk then
      let args := e.getAppArgs
      -- FuncSpec.mk σ pre post
      if args.size >= 3 then some (args[1]!, args[2]!)
      else none
    else none
  if let some result := check val then return some result
  -- Second try: one level of delta-reduction (unfold the definition name)
  if let some val' ← unfoldDefinition? val then
    if let some result := check val' then return some result
  return none

/-! # Utility: collect transitive axiom dependencies -/

/-- Collect all axiom names that `declName` transitively depends on.
    This is the MetaM equivalent of `#print axioms`. -/
partial def collectAxioms (env : Environment) (declName : Name) : NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut axioms : NameSet := {}
  let mut worklist : List Name := [declName]
  while h : !worklist.isEmpty do
    let name := worklist.head (by simp_all)
    worklist := worklist.tail
    if visited.contains name then continue
    visited := visited.insert name
    match env.find? name with
    | none => pure ()  -- external or builtin
    | some ci =>
      if ci.isAxiom then
        axioms := axioms.insert name
      -- Add all constants referenced in the type and value
      let typeConsts := ci.type.getUsedConstants
      for c in typeConsts do
        if !visited.contains c then
          worklist := c :: worklist
      match ci with
      | ConstantInfo.defnInfo v =>
        let valConsts := v.value.getUsedConstants
        for c in valConsts do
          if !visited.contains c then
            worklist := c :: worklist
      | ConstantInfo.thmInfo v =>
        let valConsts := v.value.getUsedConstants
        for c in valConsts do
          if !visited.contains c then
            worklist := c :: worklist
      | _ => pure ()
  return axioms

/-! # Check 1: Axiom Audit -/

/-- Flag declarations that depend on `sorryAx` or `Lean.trustCompiler`.
    These indicate unproven obligations or trusted native code. -/
def axiomAudit (env : Environment) (declName : Name) : Option MessageData := Id.run do
  let axioms := collectAxioms env declName
  let mut bad : Array Name := #[]
  for n in axioms do
    if n == ``sorryAx || n == ``Lean.trustCompiler then
      bad := bad.push n
  if bad.isEmpty then return none
  else return some m!"depends on unacceptable axioms: {bad.toList}"

/-! # Check 2: Spec Strength — does postcondition constrain ret__val? -/

/-- Check if an expression contains a reference to a name containing "ret__val".
    Walks the expression tree syntactically (no reduction). -/
partial def exprMentionsRetVal (e : Expr) : Bool :=
  match e with
  | .app f a => exprMentionsRetVal f || exprMentionsRetVal a
  | .lam _ d b _ => exprMentionsRetVal d || exprMentionsRetVal b
  | .forallE _ d b _ => exprMentionsRetVal d || exprMentionsRetVal b
  | .letE _ t v b _ => exprMentionsRetVal t || exprMentionsRetVal v || exprMentionsRetVal b
  | .proj n _ e => strContains n.toString "ret__val" || exprMentionsRetVal e
  | .const n _ => strContains n.toString "ret__val"
  | .mdata _ e => exprMentionsRetVal e
  | _ => false

/-- Check if an expression is a reflexive equality (x = x pattern).
    Uses syntactic equality only — no reduction. -/
private def isReflEqSyntactic (e : Expr) : Bool :=
  if e.getAppFn.isConstOf ``Eq then
    let args := e.getAppArgs
    args.size >= 3 && args[1]! == args[2]!
  else false

/-- Walk a proposition syntactically and check if every leaf is trivial:
    - reflexive equality (x = x)
    - True
    - conjunction of trivials
    - implication/forall where the conclusion is trivial -/
partial def isTrivialPropSyntactic (e : Expr) : Bool :=
  if e.isConstOf ``True then true
  else if isReflEqSyntactic e then true
  else if e.getAppFn.isConstOf ``And then
    let args := e.getAppArgs
    args.size >= 2 && isTrivialPropSyntactic args[0]! && isTrivialPropSyntactic args[1]!
  else if e.isForall then
    -- For ∀ x, body or P → Q, check the body
    isTrivialPropSyntactic e.bindingBody!
  else false

/-- Spec strength check: flag FuncSpec definitions whose postcondition
    doesn't meaningfully constrain ret__val.

    Heuristic approach (purely syntactic, no reduction):
    1. Check if post mentions ret__val anywhere in its syntax tree
    2. Check if post's body contains only reflexive equalities / True

    Limitation: this is syntactic only. Won't catch tautologies hidden behind
    definitions, but also won't explode on large ProgramState types. -/
def specStrength (env : Environment) (declName : Name) : MetaM (Option MessageData) := do
  let some ci := env.find? declName | return none
  -- Check type is FuncSpec
  let ty := ci.type
  unless ty.getAppFn.isConstOf ``FuncSpec do return none
  -- Get the value and extract pre/post
  let some val := ci.value? | return none
  let some (_pre, post) ← extractFuncSpecFields val | return none
  -- Check 1: does post mention ret__val at all?
  let mentionsRet := exprMentionsRetVal post
  -- Check 2: is post body trivial? Walk into lambda binders to get to the Prop body
  let postBody := match post with
    | .lam _ _ (.lam _ _ body _) _ => body  -- fun r s => body
    | .lam _ _ body _ => body               -- fun r => body (partial application)
    | _ => post
  let isTrivial := isTrivialPropSyntactic postBody
  if isTrivial then
    return some m!"postcondition is trivially true (all conjuncts are reflexive equalities or True)"
  if !mentionsRet then
    return some m!"postcondition does not reference ret__val — may not constrain return value"
  return none

/-! # Check 3: satisfiedBy Target -/

/-- Check if a theorem proving `FuncSpec.satisfiedBy spec body` references
    an auto-generated L1 body (in a Generated.* or Module.l1_* namespace).

    We inspect the type of the declaration for the satisfiedBy pattern and
    extract the body argument. Does not reduce anything. -/
def satisfiedByTarget (env : Environment) (declName : Name) : MetaM (Option MessageData) := do
  let some ci := env.find? declName | return none
  unless isThm ci do return none
  let ty := ci.type
  -- Look for FuncSpec.satisfiedBy in the type (may be behind foralls for universe params)
  let fn := ty.getAppFn
  unless fn.isConstOf ``FuncSpec.satisfiedBy do return none
  let args := ty.getAppArgs
  -- satisfiedBy args: [σ, spec, body]
  unless args.size >= 3 do return none
  let body := args[2]!
  let bodyConst := body.getAppFn
  match bodyConst with
  | .const name _ =>
    let nameStr := name.toString
    let isGenerated := strContains nameStr "l1_" && strContains nameStr "_body"
    if isGenerated then return none
    else return some m!"satisfiedBy target `{name}` does not look like an auto-generated L1 body (expected *l1_*_body pattern)"
  | _ =>
    return some m!"satisfiedBy target is not a named constant — may be a hand-written body"

/-! # Check 4: Tautological Postcondition -/

/-- Check if a FuncSpec's postcondition is tautological: provable for all inputs.

    Uses the same syntactic trivial-prop check as specStrength but reported
    under a different category. A postcondition is tautological if it can be
    proved for all inputs without any domain knowledge.

    Known limitation: only catches syntactically obvious tautologies
    (x = x, True, conjunctions thereof, implications with trivial consequent).
    Does NOT use isDefEq or whnf to avoid heartbeat explosion on large states. -/
def tautologicalPost (env : Environment) (declName : Name) : MetaM (Option MessageData) := do
  let some ci := env.find? declName | return none
  unless ci.type.getAppFn.isConstOf ``FuncSpec do return none
  let some val := ci.value? | return none
  let some (_pre, post) ← extractFuncSpecFields val | return none
  -- Walk into lambda binders
  let postBody := match post with
    | .lam _ _ (.lam _ _ body _) _ => body
    | .lam _ _ body _ => body
    | _ => post
  if isTrivialPropSyntactic postBody then
    return some m!"postcondition is tautological — provable for all inputs without any assumptions"
  return none

/-! # Check 5: Vacuous Precondition -/

/-- Check if a FuncSpec's precondition is vacuously false (no state satisfies it).

    Conservative check: only catches `fun _ => False` syntactically.

    Known limitation: only catches the trivial case. Complex unsatisfiable
    preconditions require a decision procedure we don't have without
    running tactics. A TODO for future work: try `decide` in a tactic block. -/
def vacuousPre (env : Environment) (declName : Name) : MetaM (Option MessageData) := do
  let some ci := env.find? declName | return none
  unless ci.type.getAppFn.isConstOf ``FuncSpec do return none
  let some val := ci.value? | return none
  let some (pre, _post) ← extractFuncSpecFields val | return none
  -- Check if pre body is `False` after stripping lambda
  let preBody := match pre with
    | .lam _ _ body _ => body
    | _ => pre
  if preBody.isConstOf ``False then
    return some m!"precondition is vacuous — no state can satisfy it (body is False)"
  return none

/-! # Runner: execute all checks on the environment -/

/-- Result of a single lint check on a single declaration. -/
structure LintResult where
  declName : Name
  checkName : String
  message : MessageData

/-- Run all semantic lint checks on declarations in the environment.
    Only processes non-internal declarations. Axiom audit is restricted
    to theorems; spec checks are restricted to FuncSpec definitions. -/
def runAllChecks (env : Environment) : MetaM (Array LintResult) := do
  let mut results : Array LintResult := #[]
  let decls := env.constants.fold (init := #[]) fun acc name _ci =>
    if name.isInternal then acc
    else acc.push name
  for name in decls do
    -- Check 1: axiom audit (only on theorems)
    if let some ci := env.find? name then
      if isThm ci then
        if let some msg := axiomAudit env name then
          results := results.push { declName := name, checkName := "axiom_audit", message := msg }
    -- Check 2: spec strength (only on FuncSpec defs)
    if let some msg ← specStrength env name then
      results := results.push { declName := name, checkName := "spec_strength", message := msg }
    -- Check 3: satisfiedBy target (only on theorems)
    if let some msg ← satisfiedByTarget env name then
      results := results.push { declName := name, checkName := "satisfiedBy_target", message := msg }
    -- Check 4: tautological postcondition (only on FuncSpec defs)
    if let some msg ← tautologicalPost env name then
      results := results.push { declName := name, checkName := "tautological_post", message := msg }
    -- Check 5: vacuous precondition (only on FuncSpec defs)
    if let some msg ← vacuousPre env name then
      results := results.push { declName := name, checkName := "vacuous_pre", message := msg }
  return results

/-- Pretty-print lint results, grouped by check name. -/
def formatResults (results : Array LintResult) : MessageData :=
  if results.isEmpty then
    m!"Clift semantic lint: all checks passed (0 findings)"
  else
    let checkNames := results.foldl (init := #[]) fun acc r =>
      if acc.contains r.checkName then acc else acc.push r.checkName
    let parts := checkNames.foldl (init := #[]) fun acc checkName =>
      let findings := results.filter fun r => r.checkName == checkName
      let header := m!"--- {checkName} ({findings.size} finding(s)) ---"
      let items := findings.map fun r => m!"  {r.declName}: {r.message}"
      acc ++ #[header] ++ items
    let summary := m!"Clift semantic lint: {results.size} finding(s)"
    MessageData.joinSep (summary :: parts.toList) (m!"\n")

/-! # Command: #clift_lint -/

/-- `#clift_lint` runs all Clift semantic lint checks on the current environment.
    Import your proof modules before calling this to check them. -/
elab "#clift_lint" : command => do
  let env ← getEnv
  let results ← liftTermElabM <| runAllChecks env
  if results.isEmpty then
    logInfo (formatResults results)
  else
    logWarning (formatResults results)

/-- `#clift_lint_axioms declName` runs just the axiom audit on a single declaration. -/
elab "#clift_lint_axioms " id:ident : command => do
  let env ← getEnv
  let name := id.getId
  let some _ci := env.find? name | throwError "unknown declaration: {name}"
  match axiomAudit env name with
  | none => logInfo m!"{name}: axiom audit passed"
  | some msg => logWarning m!"{name}: {msg}"

end Clift.Lint

/-! # Self-test: validate checks against synthetic specs -/

section SemanticLintSelfTest

open Clift.Lint

-- Test spec: tautological postcondition (post is True)
private def _selftest_taut_spec : FuncSpec Nat where
  pre := fun _s => True
  post := fun _r _s => True

-- Test spec: reflexive equality postcondition (s = s)
private def _selftest_refl_spec : FuncSpec Nat where
  pre := fun s => s > 0
  post := fun _r s => s = s

-- Test spec: vacuous precondition (False)
private def _selftest_vacuous_spec : FuncSpec Nat where
  pre := fun _s => False
  post := fun _r _s => True

-- Test spec: reasonable (constrains something)
private def _selftest_good_spec : FuncSpec Nat where
  pre := fun s => s > 0
  post := fun r _s => r = Except.ok ()

-- Validate: tautological check fires on taut_spec
#eval show Lean.MetaM _ from do
  let env ← Lean.getEnv
  let result ← tautologicalPost env ``_selftest_taut_spec
  assert! result.isSome
  Lean.logInfo m!"tautological_post: correctly flagged _selftest_taut_spec"

-- Validate: tautological check fires on refl_spec
#eval show Lean.MetaM _ from do
  let env ← Lean.getEnv
  let result ← tautologicalPost env ``_selftest_refl_spec
  assert! result.isSome
  Lean.logInfo m!"tautological_post: correctly flagged _selftest_refl_spec"

-- Validate: vacuous check fires on vacuous_spec
#eval show Lean.MetaM _ from do
  let env ← Lean.getEnv
  let result ← vacuousPre env ``_selftest_vacuous_spec
  assert! result.isSome
  Lean.logInfo m!"vacuous_pre: correctly flagged _selftest_vacuous_spec"

-- Validate: tautological check does NOT fire on good_spec
#eval show Lean.MetaM _ from do
  let env ← Lean.getEnv
  let result ← tautologicalPost env ``_selftest_good_spec
  assert! result.isNone
  Lean.logInfo m!"tautological_post: correctly passed _selftest_good_spec"

-- Validate: vacuous check does NOT fire on good_spec
#eval show Lean.MetaM _ from do
  let env ← Lean.getEnv
  let result ← vacuousPre env ``_selftest_good_spec
  assert! result.isNone
  Lean.logInfo m!"vacuous_pre: correctly passed _selftest_good_spec"

-- Validate: spec_strength flags taut_spec (no ret__val)
#eval show Lean.MetaM _ from do
  let env ← Lean.getEnv
  let result ← specStrength env ``_selftest_taut_spec
  assert! result.isSome
  Lean.logInfo m!"spec_strength: correctly flagged _selftest_taut_spec"

-- Validate: spec_strength flags refl_spec (ret__val not mentioned)
#eval show Lean.MetaM _ from do
  let env ← Lean.getEnv
  let result ← specStrength env ``_selftest_refl_spec
  assert! result.isSome
  Lean.logInfo m!"spec_strength: correctly flagged _selftest_refl_spec"

-- Validate: axiom audit on a clean theorem (no sorry)
-- FuncSpec.call_spec is a real theorem, should not have sorryAx
#eval show Lean.MetaM _ from do
  let env ← Lean.getEnv
  let result := axiomAudit env ``FuncSpec.call_spec
  assert! result.isNone
  Lean.logInfo m!"axiom_audit: correctly passed FuncSpec.call_spec (no sorry)"

end SemanticLintSelfTest
