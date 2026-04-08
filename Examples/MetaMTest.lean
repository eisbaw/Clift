-- MetaM feasibility test
--
-- Validates that CSimpl types are MetaM-friendly:
-- 1. Can we construct CSimpl terms programmatically?
-- 2. Can we construct Exec proof terms?
-- 3. Can we inspect CSimpl term structure?
--
-- This is Phase 0 risk mitigation for Lean 4 metaprogramming (Risk #4).

import Clift.CSemantics.HoareDef
import Lean

open Lean Meta Elab Term Tactic

/-! # Test 1: Construct a CSimpl.skip term in MetaM -/

/-- Build CSimpl.skip for a given state type σ. -/
def mkCSimplSkip (σ : Expr) : MetaM Expr := do
  return mkApp (.const ``CSimpl.skip []) σ

/-- Construct a basic (state transformation) CSimpl node. -/
def mkCSimplBasic (σ f : Expr) : MetaM Expr := do
  return mkApp2 (.const ``CSimpl.basic []) σ f

/-- Construct a seq (sequential composition) CSimpl node. -/
def mkCSimplSeq (σ c₁ c₂ : Expr) : MetaM Expr := do
  return mkApp3 (.const ``CSimpl.seq []) σ c₁ c₂

/-- Build CSimpl.throw for a given state type. -/
def mkCSimplThrow (σ : Expr) : MetaM Expr := do
  return mkApp (.const ``CSimpl.throw []) σ

/-- Build CSimpl.catch. -/
def mkCSimplCatch (σ body handler : Expr) : MetaM Expr := do
  return mkApp3 (.const ``CSimpl.catch []) σ body handler

/-- Build CSimpl.cond. -/
def mkCSimplCond (σ b c₁ c₂ : Expr) : MetaM Expr := do
  return mkApp4 (.const ``CSimpl.cond []) σ b c₁ c₂

/-! # Test: Elaborate and verify CSimpl terms -/

/-- Build a CSimpl.skip Nat and verify it type-checks. -/
elab "test_mk_skip" : term => do
  let natExpr := .const ``Nat []
  let skipExpr ← mkCSimplSkip natExpr
  let ty ← inferType skipExpr
  logInfo m!"Constructed: {skipExpr} : {ty}"
  return skipExpr

-- AC #1: MetaM program that constructs CSimpl.skip compiles
#check (test_mk_skip : CSimpl Nat)

/-! # Test 2: Construct an Exec proof term for skip -/

/-- Build a proof of `Exec Γ .skip s (.normal s)`.
    This validates that we can programmatically construct proof terms. -/
def mkExecSkipProof (σ Γ s : Expr) : MetaM Expr := do
  return mkApp3 (.const ``Exec.skip []) σ Γ s

/-- Test building an Exec.skip proof. -/
elab "test_exec_skip_proof" : term => do
  let natExpr := .const ``Nat []
  let gammaExpr := mkApp (.const ``ProcEnv.empty []) natExpr
  let zeroExpr := .const ``Nat.zero []
  let proofExpr ← mkExecSkipProof natExpr gammaExpr zeroExpr
  let ty ← inferType proofExpr
  logInfo m!"Exec proof: {proofExpr} : {ty}"
  return proofExpr

-- AC #2: MetaM program that constructs an Exec proof compiles
#check (test_exec_skip_proof : Exec ProcEnv.empty .skip 0 (.normal 0))

/-! # Test 3: Pattern match on CSimpl constructors in MetaM -/

/-- Inspect a CSimpl expression and identify its top-level constructor. -/
def inspectCSimpl (e : Expr) : MetaM String := do
  let e ← whnfD e
  match e.getAppFn with
  | .const ``CSimpl.skip _ => return "skip"
  | .const ``CSimpl.basic _ => return "basic"
  | .const ``CSimpl.seq _ => return "seq"
  | .const ``CSimpl.cond _ => return "cond"
  | .const ``CSimpl.while _ => return "while"
  | .const ``CSimpl.call _ => return "call"
  | .const ``CSimpl.guard _ => return "guard"
  | .const ``CSimpl.throw _ => return "throw"
  | .const ``CSimpl.catch _ => return "catch"
  | .const ``CSimpl.spec _ => return "spec"
  | .const ``CSimpl.dynCom _ => return "dynCom"
  | _ => return s!"unknown: {e}"

/-- Command to inspect CSimpl terms. -/
elab "#inspect_csimpl" t:term : command => do
  Elab.Command.liftTermElabM do
    let e ← elabTerm t none
    let result ← inspectCSimpl e
    logInfo m!"CSimpl constructor: {result}"

-- AC #3: Can inspect CSimpl term structure
#inspect_csimpl (CSimpl.skip : CSimpl Nat)
#inspect_csimpl (CSimpl.basic (fun n : Nat => n + 1) : CSimpl Nat)
#inspect_csimpl (CSimpl.seq CSimpl.skip CSimpl.skip : CSimpl Nat)
#inspect_csimpl (CSimpl.throw : CSimpl Nat)
#inspect_csimpl (CSimpl.catch CSimpl.skip CSimpl.skip : CSimpl Nat)

/-! # Test 4: Build a complex CSimpl term matching max_body structure -/

/-- Build a CSimpl term that mirrors the structure of max_body,
    but for Nat state. Validates MetaM can build the same
    structures the CImporter needs to generate. -/
def mkSimpleMaxBody : MetaM Expr := do
  let natExpr := Expr.const ``Nat []
  let skip ← mkCSimplSkip natExpr
  let throw ← mkCSimplThrow natExpr
  -- identity function: fun (s : Nat) => s
  let idFun := .lam `s natExpr (.bvar 0) .default
  let basic ← mkCSimplBasic natExpr idFun
  -- seq basic throw
  let seqBT ← mkCSimplSeq natExpr basic throw
  -- condition: fun (_ : Nat) => true
  let condFun := .lam `s natExpr (.const ``Bool.true []) .default
  -- cond condFun seqBT seqBT
  let condExpr ← mkCSimplCond natExpr condFun seqBT seqBT
  -- catch condExpr skip
  mkCSimplCatch natExpr condExpr skip

elab "test_mk_max_structure" : term => do
  let expr ← mkSimpleMaxBody
  let ty ← inferType expr
  logInfo m!"Max-like CSimpl: {ty}"
  let kind ← inspectCSimpl expr
  logInfo m!"Top-level constructor: {kind}"
  return expr

#check (test_mk_max_structure : CSimpl Nat)

/-! # Feasibility assessment -/

/-- Summary: MetaM is fully capable of building CSimpl terms and Exec proofs.

    Results:
    1. CSimpl.skip construction: works (mkApp on constructor)
    2. CSimpl.basic/seq/cond/catch construction: works (mkAppN on constructors)
    3. Exec proof term construction: works (constructor application)
    4. CSimpl pattern matching: works (getAppFn + const matching)
    5. Complex term construction: works (max_body-like structure)

    Assessment: GO. The lifting pipeline can proceed with MetaM.

    Notes:
    - CSimpl is a simple inductive, no universe issues
    - Lambda construction via Expr.lam is straightforward
    - Proof terms are direct constructor applications
    - For the actual lifting pipeline, we will need:
      * Recursive MetaM traversal of CSimpl terms
      * Building more complex Exec derivations (while, call)
      * Constructing corres proof terms
    - These are all achievable with the same patterns tested here -/
theorem metam_feasibility_passes : True := trivial
