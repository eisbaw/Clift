-- L2Auto: Automatic local variable extraction (CState -> Globals)
--
-- After L1, computations operate on CState Locals = { globals : Globals, locals : Locals }.
-- L2 extracts locals into explicit function parameters so the computation
-- operates on Globals only.
--
-- Approach: "wrapper" L2 extraction.
-- Given an L1 computation m : L1Monad (CState Locals), we generate
-- l2_wrap m locs : L1Monad Globals that:
-- 1. Reconstructs the full CState from Globals + fixed locals
-- 2. Runs the L1 computation
-- 3. Projects the result back to Globals
--
-- Why not full bidirectional L2corres: the backward direction requires that
-- the final locals equal the initial locals, which is generally false.
-- We define L2corres_fwd (forward-only) which suffices for transferring
-- validHoare properties — the useful direction for verification.
--
-- Reference: Clift/Lifting/LocalVarExtract.lean (L2corres definition)

import Clift.Lifting.SimplConv
import Clift.Lifting.LocalVarExtract
import Lean

open Lean Meta Elab Command Term Tactic

/-! # l2_wrap: mechanical L2 extraction -/

/-- Wrap an L1 computation on CState into one on Globals.
    The locals are provided as a fixed parameter.

    The result type changes from (CState Locals) to Globals.
    Failure is preserved exactly. Results are projected to globals. -/
def l2_wrap {Locals : Type} (m : L1Monad (CState Locals)) (locs : Locals) : L1Monad Globals :=
  fun g =>
    let fullState : CState Locals := { globals := g, locals := locs }
    let result := m fullState
    { results := fun p => ∃ (s' : CState Locals), (p.1, s') ∈ result.results ∧ p.2 = s'.globals
      failed := result.failed }

/-! # Forward-only L2 correspondence -/

/-- Forward-only L2 correspondence.
    Sufficient for transferring Hoare properties from L1 to L2.

    Forward: every L1 result projects to an L2 result.
    Failure: if L1 fails then L2 fails (contrapositive: L2 no-fail implies L1 no-fail). -/
def L2corres_fwd {σ₁ σ₂ : Type} {α : Type}
    (proj : σ₁ → σ₂)
    (lift : σ₂ → σ₁)
    (m2 : NondetM σ₂ α)
    (m1 : NondetM σ₁ α) : Prop :=
  ∀ s₁,
    lift (proj s₁) = s₁ →
    ((m1 s₁).failed → (m2 (proj s₁)).failed) ∧
    (∀ r t₁, (r, t₁) ∈ (m1 s₁).results →
      (r, proj t₁) ∈ (m2 (proj s₁)).results)

/-- l2_wrap satisfies forward-only L2 correspondence. -/
theorem l2_wrap_corres_fwd {Locals : Type} (m : L1Monad (CState Locals)) (locs : Locals) :
    L2corres_fwd
      (fun s : CState Locals => s.globals)
      (fun g : Globals => ⟨g, locs⟩)
      (l2_wrap m locs)
      m := by
  intro s₁ hrt
  -- hrt tells us { globals := s₁.globals, locals := locs } = s₁
  -- Beta-reduce the lambdas in hrt, then use it
  simp only [] at hrt  -- beta-reduce
  have h_eq := hrt  -- now: { globals := s₁.globals, locals := locs } = s₁
  constructor
  · -- Failure forward: m fails -> l2_wrap fails
    intro hf
    show (l2_wrap m locs s₁.globals).failed
    unfold l2_wrap; simp only []
    rw [h_eq]; exact hf
  · -- Result forward: m result -> l2_wrap result
    intro r t₁ h_mem
    show (r, t₁.globals) ∈ (l2_wrap m locs s₁.globals).results
    unfold l2_wrap; simp only []
    refine ⟨t₁, ?_, rfl⟩
    rw [h_eq]; exact h_mem

/-! # Hoare transfer theorems -/

/-- Transfer validHoare from L1 (on CState) to L2 (on Globals) for l2_wrap.

    Given a validHoare triple on L1, produce one on the L2 wrapper.
    The precondition must hold for the initial state constructed from
    any globals + the fixed locals. -/
theorem l2_wrap_validHoare {Locals : Type}
    {m : L1Monad (CState Locals)} {locs : Locals}
    {P : CState Locals → Prop} {Q : Except Unit Unit → CState Locals → Prop}
    (h1 : validHoare P m Q)
    (h_init : ∀ g, P ⟨g, locs⟩) :
    validHoare
      (fun _ : Globals => True)
      (l2_wrap m locs)
      (fun r g => ∃ s' : CState Locals, s'.globals = g ∧ Q r s') := by
  intro g _
  have ⟨h_nf, h_post⟩ := h1 ⟨g, locs⟩ (h_init g)
  constructor
  · intro hf
    unfold l2_wrap at hf; simp at hf
    exact h_nf hf
  · intro r g' h_mem
    unfold l2_wrap at h_mem; simp at h_mem
    obtain ⟨s', h_mem', h_eq⟩ := h_mem
    exact ⟨s', h_eq.symm, h_post r s' h_mem'⟩

/-- Simplified version when the postcondition only depends on globals. -/
theorem l2_wrap_validHoare_globals {Locals : Type}
    {m : L1Monad (CState Locals)} {locs : Locals}
    {P : CState Locals → Prop}
    {Q_globals : Except Unit Unit → Globals → Prop}
    (h1 : validHoare P m (fun r s => Q_globals r s.globals))
    (h_init : ∀ g, P ⟨g, locs⟩) :
    validHoare
      (fun _ : Globals => True)
      (l2_wrap m locs)
      Q_globals := by
  intro g _
  have ⟨h_nf, h_post⟩ := h1 ⟨g, locs⟩ (h_init g)
  constructor
  · intro hf
    unfold l2_wrap at hf; simp at hf
    exact h_nf hf
  · intro r g' h_mem
    unfold l2_wrap at h_mem; simp at h_mem
    obtain ⟨s', h_mem', h_eq⟩ := h_mem
    have h_q := h_post r s' h_mem'
    simp at h_eq; rw [h_eq]; exact h_q

/-! # clift_l2 command: auto-generate L2 wrappers -/

/-- `clift_l2 <Module>` command: generate L2 wrappers for all L1 functions.

    For each `l1_<func>_body` in the namespace, generates:
    - `l2_<func>_body (locs : Locals) : L1Monad Globals`
    - `l2_<func>_body_corres_fwd (locs)` proving forward L2 correspondence

    Requires `clift_l1` to have been run first. -/
elab "clift_l2 " ns:ident : command => do
  let nsName := ns.getId
  let env ← getEnv

  let localsName := nsName ++ `Locals
  unless env.contains localsName do
    throwError "clift_l2: {localsName} not found"

  -- Find all l1_*_body definitions
  -- Search both map₁ and map₂ since dynamically added defs may be in either
  let mut l1Bodies : Array Name := #[]
  for (name, _) in env.constants.map₁.toList do
    if name.getPrefix == nsName then
      let nameStr := name.components.getLast!.toString
      if nameStr.startsWith "l1_" && nameStr.endsWith "_body" then
        l1Bodies := l1Bodies.push name
  for (name, _) in env.constants.map₂.toList do
    if name.getPrefix == nsName then
      let nameStr := name.components.getLast!.toString
      if nameStr.startsWith "l1_" && nameStr.endsWith "_body" then
        l1Bodies := l1Bodies.push name

  if l1Bodies.isEmpty then
    throwError "clift_l2: no l1_*_body definitions found in {nsName}. Run clift_l1 first."

  logInfo m!"clift_l2: found {l1Bodies.size} L1 bodies in {nsName}"

  for l1Name in l1Bodies do
    let l1Str := l1Name.components.getLast!.toString
    let l2Str := l1Str.replace "l1_" "l2_"
    let l2Name := nsName ++ Name.mkSimple l2Str
    let corresName := nsName ++ Name.mkSimple s!"{l2Str}_corres_fwd"

    liftTermElabM do
      let localsType := Lean.mkConst localsName
      let l1Ref := Lean.mkConst l1Name

      -- l2_<fn> (locs : Locals) : L1Monad Globals := l2_wrap l1_<fn> locs
      let l2Body := mkApp3 (.const ``l2_wrap []) localsType l1Ref (.bvar 0)
      let l2Lambda := Expr.lam `locs localsType l2Body .default

      -- Type: Locals -> L1Monad Globals
      let exceptType := mkApp2 (.const ``Except [.zero, .zero]) (.const ``Unit []) (.const ``Unit [])
      let l1MonadGlobals := mkApp2 (.const ``NondetM []) (.const ``Globals []) exceptType
      let l2Type := Expr.forallE `locs localsType l1MonadGlobals .default

      let l2Lambda ← instantiateMVars l2Lambda
      check l2Lambda

      addDecl <| Declaration.defnDecl {
        name := l2Name
        levelParams := []
        type := l2Type
        value := l2Lambda
        hints := .abbrev
        safety := .safe
      }

      -- Prove forward correspondence: fun locs => l2_wrap_corres_fwd l1_fn locs
      let corresBody := mkApp3 (.const ``l2_wrap_corres_fwd []) localsType l1Ref (.bvar 0)
      let proofVal := Expr.lam `locs localsType corresBody .default
      let proofVal ← instantiateMVars proofVal
      check proofVal
      let corresType ← inferType proofVal

      addDecl <| Declaration.thmDecl {
        name := corresName
        levelParams := []
        type := corresType
        value := proofVal
      }

    logInfo m!"clift_l2: {l1Name} -> {l2Name} + {corresName}"
