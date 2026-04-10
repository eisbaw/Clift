-- L3Auto: MetaM automation for TypeStrengthen (monad narrowing)
--
-- Given L1/L2 functions, classify each as pure/option/nondet based on
-- syntactic analysis of the L1 term structure.
--
-- Classification rules (Phase A, conservative):
--   pure:   no L1.guard, no L1.fail, no L1.while, no L1.spec
--   nondet: everything else (while loops, guards, specs, fail)
--
-- For pure functions (no while/guard/fail/spec), the L1 body is a
-- deterministic composition of modify/seq/catch/throw/condition/skip.
-- We can prove such functions never fail and produce exactly one result.
--
-- Reference: ext/AutoCorres2/type_strengthen.ML
-- Reference: Clift/Lifting/TypeStrengthen.lean (manual L3 types)

import Clift.Lifting.SimplConv
import Clift.Lifting.TypeStrengthen
import Clift.Lifting.L1Auto
import Clift.Lifting.L2Auto
import Lean

open Lean Meta Elab Command Term Tactic

/-! # Monad level classification -/

/-- Classification of a function's monad level. -/
inductive MonadLevel where
  | pure   : MonadLevel  -- No state effects, no failure
  | nondet : MonadLevel  -- Full nondeterministic monad
  deriving Repr, BEq, Inhabited

instance : ToString MonadLevel where
  toString
    | .pure   => "pure"
    | .nondet => "nondet"

/-! # Syntactic classifier

Walk an L1 expression (which is an application of L1 combinators) and check
whether any guard/fail/while/spec constructors appear. If none do, the
function is pure — it's a deterministic composition of modify/seq/catch/
throw/condition/skip. -/

/-- Check whether an L1Monad expression contains guard, fail, while, or spec.
    Returns true if the term is "pure" (contains none of these).
    The input should be the L1 body as constructed by csimplToL1
    (applications of L1.skip, L1.modify, etc.). We do NOT whnf here
    because these are definitions, not constructors — whnf would
    unfold them to their lambda bodies. -/
partial def isPureL1 (e : Expr) : MetaM Bool := do
  match e.getAppFn with
  | .const ``L1.skip _ => return true
  | .const ``L1.modify _ => return true
  | .const ``L1.throw _ => return true
  | .const ``L1.seq _ =>
    let args := e.getAppArgs
    if args.size > 2 then
      let r1 ← isPureL1 args[1]!
      let r2 ← isPureL1 args[2]!
      return r1 && r2
    else return false
  | .const ``L1.condition _ =>
    let args := e.getAppArgs
    if args.size > 3 then
      let r1 ← isPureL1 args[2]!
      let r2 ← isPureL1 args[3]!
      return r1 && r2
    else return false
  | .const ``L1.catch _ =>
    let args := e.getAppArgs
    if args.size > 2 then
      let r1 ← isPureL1 args[1]!
      let r2 ← isPureL1 args[2]!
      return r1 && r2
    else return false
  | .const ``L1.guard _ => return false
  | .const ``L1.fail _ => return false
  | .const ``L1.while _ => return false
  | .const ``L1.spec _ => return false
  | _ => return false  -- Unknown constructor: conservatively nondet

/-- Classify an L1 function as pure or nondet. -/
def classifyL1 (l1Body : Expr) : MetaM MonadLevel := do
  let pure ← isPureL1 l1Body
  return if pure then .pure else .nondet

/-! # Pure function extraction

For a pure L1 body (no guard/fail/while/spec), we can extract the
deterministic state transformation function.

A pure L1 body is a composition of:
  L1.skip       -> identity
  L1.modify f   -> apply f
  L1.throw      -> signal return (caught by catch)
  L1.seq m1 m2  -> run m1, if ok continue with m2, if error propagate
  L1.condition b t e -> branch on b
  L1.catch m h  -> run m, if error run h on error state

We extract a function `σ -> σ` that gives the final state after running
the L1 body. The L1 body uses catch/throw for function return, so we
model the "running" state as Option σ (None = returned/abrupt).

Actually, the L1 body's results are `Except Unit Unit × σ`, and for
functions with return-via-throw, the useful result is the state when
the function exits (either normally or via catch).

For the standard pattern `catch (seq <body> (seq (modify set-retval) throw)) skip`:
- The body computes, then sets ret_val and throws
- The catch catches the throw and runs skip
- Result: the final state with ret_val set

Rather than trying to extract a pure function from the L1 structure,
we prove that the L1 body is deterministic: it never fails and produces
exactly one result for each input state. This is the L3 contribution
for Phase A.

The proof obligation for a pure-classified function:
  ∀ s, ¬(l1_body s).failed ∧ ∃! s', (Except.ok (), s') ∈ (l1_body s).results
-/

/-- A pure L1 computation: never fails and produces exactly one ok-result.
    This is the "deterministic + total" characterization. -/
def L1Pure {σ : Type} (m : L1Monad σ) : Prop :=
  ∀ s, ¬(m s).failed ∧
    ∃ s', (Except.ok (), s') ∈ (m s).results ∧
      ∀ r t, (r, t) ∈ (m s).results → t = s' ∧ (r = Except.ok () ∨ r = Except.error ())

/-! # L1Pure lemmas for each pure combinator -/

-- Note: L1Pure (requiring ∃ s' with ok-result) doesn't hold for throw alone,
-- since throw only produces error results. But throw appears inside catch,
-- and catch converts error to ok. So we use L1Deterministic instead, which
-- allows either ok or error as the single result.

/-- A deterministic L1 computation: never fails and produces exactly one result. -/
def L1Deterministic {σ : Type} (m : L1Monad σ) : Prop :=
  ∀ s, ¬(m s).failed ∧
    ∃ r s', (r, s') ∈ (m s).results ∧
      ∀ r' t', (r', t') ∈ (m s).results → r' = r ∧ t' = s'

-- This is provable for skip, modify, throw, and compositions of them.

theorem L1Det_skip {σ : Type} : L1Deterministic (L1.skip : L1Monad σ) := by
  intro s
  refine ⟨by simp [L1.skip, NondetM.pure], Except.ok (), s, rfl, ?_⟩
  intro r' t' h
  simp [L1.skip, NondetM.pure] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl⟩

theorem L1Det_modify {σ : Type} (f : σ → σ) :
    L1Deterministic (L1.modify f : L1Monad σ) := by
  intro s
  refine ⟨by simp [L1.modify], Except.ok (), f s, rfl, ?_⟩
  intro r' t' h
  simp [L1.modify] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl⟩

theorem L1Det_throw {σ : Type} : L1Deterministic (L1.throw : L1Monad σ) := by
  intro s
  refine ⟨by simp [L1.throw, NondetM.pure], Except.error (), s, rfl, ?_⟩
  intro r' t' h
  simp [L1.throw, NondetM.pure] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl⟩

/-! ## L1Det_seq: deterministic sequencing

If m1 and m2 are deterministic, then seq m1 m2 is deterministic.
Case analysis on whether m1 returns ok or error. -/

theorem L1Det_seq {σ : Type} {m1 m2 : L1Monad σ}
    (h1 : L1Deterministic m1) (h2 : L1Deterministic m2) :
    L1Deterministic (L1.seq m1 m2) := by
  intro s
  obtain ⟨h1_nf, r1, s1, h1_mem, h1_uniq⟩ := h1 s
  cases r1 with
  | ok _ =>
    -- m1 returns ok: seq continues with m2 at s1
    obtain ⟨h2_nf, r2, s2, h2_mem, h2_uniq⟩ := h2 s1
    constructor
    · -- Not failed
      intro hf
      simp [L1.seq] at hf
      rcases hf with hf1 | ⟨s', h_mem, hf2⟩
      · exact h1_nf hf1
      · have ⟨_, hs⟩ := h1_uniq _ _ h_mem
        rw [hs] at hf2
        exact h2_nf hf2
    · refine ⟨r2, s2, ?_, ?_⟩
      · simp [L1.seq]
        exact Or.inl ⟨s1, h1_mem, h2_mem⟩
      · intro r' t' h_mem'
        simp [L1.seq] at h_mem'
        rcases h_mem' with ⟨s', h_s'_mem, h_t'_mem⟩ | ⟨h_err, _⟩
        · have ⟨_, hs'⟩ := h1_uniq _ _ h_s'_mem
          rw [hs'] at h_t'_mem
          exact h2_uniq _ _ h_t'_mem
        · -- m1 returned error, but we assumed ok
          simp at h_err
          have ⟨hr, _⟩ := h1_uniq _ _ h_err
          cases hr
  | error _ =>
    -- m1 returns error: seq propagates error
    constructor
    · intro hf
      simp [L1.seq] at hf
      rcases hf with hf1 | ⟨s', h_mem, _⟩
      · exact h1_nf hf1
      · have ⟨hr, _⟩ := h1_uniq _ _ h_mem
        cases hr
    · refine ⟨Except.error (), s1, ?_, ?_⟩
      · simp [L1.seq]
        exact Or.inr ⟨h1_mem, rfl⟩
      · intro r' t' h_mem'
        simp [L1.seq] at h_mem'
        rcases h_mem' with ⟨s', h_s'_mem, h_t'_mem⟩ | ⟨h_err, h_rfl⟩
        · have ⟨hr, _⟩ := h1_uniq _ _ h_s'_mem
          cases hr
        · have ⟨_, hs⟩ := h1_uniq _ _ h_err
          exact ⟨h_rfl, hs⟩

/-! ## L1Det_condition: deterministic branching -/

theorem L1Det_condition {σ : Type} {b : σ → Bool} {m1 m2 : L1Monad σ}
    (h1 : L1Deterministic m1) (h2 : L1Deterministic m2) :
    L1Deterministic (L1.condition b m1 m2) := by
  intro s
  unfold L1.condition
  cases hb : b s
  · exact h2 s
  · exact h1 s

/-! ## L1Det_catch: deterministic catch -/

theorem L1Det_catch {σ : Type} {m1 m2 : L1Monad σ}
    (h1 : L1Deterministic m1) (h2 : L1Deterministic m2) :
    L1Deterministic (L1.catch m1 m2) := by
  intro s
  obtain ⟨h1_nf, r1, s1, h1_mem, h1_uniq⟩ := h1 s
  cases r1 with
  | ok _ =>
    -- Body returns ok: catch passes it through
    constructor
    · intro hf
      simp [L1.catch] at hf
      rcases hf with hf1 | ⟨s', h_err, _⟩
      · exact h1_nf hf1
      · have ⟨hr, _⟩ := h1_uniq _ _ h_err
        cases hr
    · refine ⟨Except.ok (), s1, ?_, ?_⟩
      · simp [L1.catch]
        exact Or.inl ⟨h1_mem, rfl⟩
      · intro r' t' h_mem'
        simp [L1.catch] at h_mem'
        rcases h_mem' with ⟨h_ok, h_rfl⟩ | ⟨s', h_err, _⟩
        · have ⟨_, hs⟩ := h1_uniq _ _ h_ok
          exact ⟨h_rfl, hs⟩
        · have ⟨hr, _⟩ := h1_uniq _ _ h_err
          cases hr
  | error _ =>
    -- Body returns error: catch runs handler at s1
    obtain ⟨h2_nf, r2, s2, h2_mem, h2_uniq⟩ := h2 s1
    constructor
    · intro hf
      simp [L1.catch] at hf
      rcases hf with hf1 | ⟨s', h_err, hf2⟩
      · exact h1_nf hf1
      · have ⟨_, hs⟩ := h1_uniq _ _ h_err
        rw [hs] at hf2
        exact h2_nf hf2
    · refine ⟨r2, s2, ?_, ?_⟩
      · simp [L1.catch]
        exact Or.inr ⟨s1, h1_mem, h2_mem⟩
      · intro r' t' h_mem'
        simp [L1.catch] at h_mem'
        rcases h_mem' with ⟨h_ok, _⟩ | ⟨s', h_err, h_rest⟩
        · have ⟨hr, _⟩ := h1_uniq _ _ h_ok
          cases hr
        · have ⟨_, hs⟩ := h1_uniq _ _ h_err
          rw [hs] at h_rest
          exact h2_uniq _ _ h_rest

/-! # clift_l3: command to classify and annotate functions -/

/-- Find all l1_*_body definitions in a namespace. -/
private def findL1Bodies (ns : Name) : MetaM (Array (Name × Expr)) := do
  let env ← getEnv
  let mut results : Array (Name × Expr) := #[]
  -- Search both maps since L1 defs added dynamically may be in map₂
  for (name, info) in env.constants.map₁.toList do
    if name.getPrefix == ns then
      let nameStr := name.components.getLast!.toString
      if nameStr.startsWith "l1_" && nameStr.endsWith "_body" then
        results := results.push (name, info.type)
  for (name, info) in env.constants.map₂.toList do
    if name.getPrefix == ns then
      let nameStr := name.components.getLast!.toString
      if nameStr.startsWith "l1_" && nameStr.endsWith "_body" then
        results := results.push (name, info.type)
  return results

/-- Classify and report monad levels for all L1 functions in a namespace.
    Also generates L1Deterministic proofs for pure functions.

    `clift_l3 <Module>` will:
    1. Find all l1_*_body definitions
    2. Classify each as pure or nondet
    3. For pure functions, try to prove L1Deterministic by tactic
    4. Report the classification -/
elab "clift_l3 " ns:ident : command => do
  let nsName := ns.getId
  let l1Bodies ← liftTermElabM <| findL1Bodies nsName

  if l1Bodies.isEmpty then
    throwError "clift_l3: no l1_*_body definitions found in {nsName}. Run clift_l1 first."

  logInfo m!"clift_l3: found {l1Bodies.size} L1 bodies in {nsName}"

  for (l1Name, _) in l1Bodies do
    liftTermElabM do
      let l1Ref := Lean.mkConst l1Name
      let l1Val ← unfoldDefinition l1Ref
      let level ← classifyL1 l1Val
      let l1Str := l1Name.components.getLast!.toString
      let l3Str := l1Str.replace "l1_" "l3_"

      match level with
      | .pure =>
        logInfo m!"clift_l3: {l1Name} classified as PURE"
        -- Generate L1Deterministic proof for pure functions
        let detName := nsName ++ Name.mkSimple s!"{l3Str}_det"
        let levelName := nsName ++ Name.mkSimple s!"{l3Str}_level"

        -- Get σ from the L1 body's type
        -- The type is NondetM σ (Except Unit Unit) or the abbrev L1Monad σ
        let l1Type ← inferType l1Ref
        -- Try to match NondetM σ α pattern (before whnf unfolds to function type)
        let σ ← if l1Type.isAppOf ``NondetM then
            pure l1Type.getAppArgs[0]!
          else
            -- Fallback: get from the l1Bodies tuple which has the type
            throwError "clift_l3: cannot extract state type from {l1Type}"
        let detType := mkApp2 (.const ``L1Deterministic []) σ l1Ref

        let proof ← mkFreshExprMVar detType
        let mvarId := proof.mvarId!

        let goals ← Tactic.run mvarId do
          -- Unfold the L1 definition, then apply L1Det lemmas
          evalTactic (← `(tactic| unfold $(mkIdent l1Name)))
          evalTactic (← `(tactic| repeat (first
            | exact L1Det_skip
            | exact L1Det_throw
            | apply L1Det_modify
            | apply L1Det_seq
            | apply L1Det_condition
            | apply L1Det_catch)))

        if goals.isEmpty then
          let proofVal ← instantiateMVars proof
          addDecl <| Declaration.thmDecl {
            name := detName
            levelParams := []
            type := detType
            value := proofVal
          }
          logInfo m!"clift_l3: {detName} proved (L1Deterministic)"
        else
          logWarning m!"clift_l3: could not prove L1Deterministic for {l1Name} ({goals.length} goals remaining)"

        -- Store level annotation as a trivial definition
        let levelType := .const ``MonadLevel []
        let levelVal := .const ``MonadLevel.pure []
        addDecl <| Declaration.defnDecl {
          name := levelName
          levelParams := []
          type := levelType
          value := levelVal
          hints := .abbrev
          safety := .safe
        }

      | .nondet =>
        logInfo m!"clift_l3: {l1Name} classified as NONDET"
        let levelName := nsName ++ Name.mkSimple s!"{l3Str}_level"
        let levelType := .const ``MonadLevel []
        let levelVal := .const ``MonadLevel.nondet []
        addDecl <| Declaration.defnDecl {
          name := levelName
          levelParams := []
          type := levelType
          value := levelVal
          hints := .abbrev
          safety := .safe
        }
