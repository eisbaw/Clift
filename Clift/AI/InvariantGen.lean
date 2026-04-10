-- AI-assisted loop invariant generation framework
--
-- Architecture:
-- 1. InvariantSuggestion: a proposed loop invariant (sigma -> Prop)
-- 2. LoopContext: serializable context for a while loop (condition, body, pre, post)
-- 3. InvariantOracle: interface for invariant generation (mock or LLM)
-- 4. checkInvariant: verify a suggested invariant satisfies VCs
-- 5. Soundness: accepted invariants yield kernel-checked Hoare triples
--
-- Key principle: the invariant source is UNTRUSTED. Whether it comes from
-- an LLM, a human, or a random generator, the Lean kernel checks it.
-- The AI is an optimization (faster invariant discovery), not a trust extension.
--
-- Reference: plan.md Phase 4, AI Integration section
-- Reference: task-0099

import Clift.Lifting.WP
import Clift.Lifting.L1HoareRules

/-! # InvariantSuggestion: a proposed loop invariant -/

/-- A suggested loop invariant: just a predicate on the state type.
    The source of the suggestion is irrelevant to soundness. -/
structure InvariantSuggestion (σ : Type) where
  /-- The invariant predicate -/
  inv : σ → Prop
  /-- Human-readable description (for logging/debugging) -/
  description : String

/-! # LoopContext: what the AI needs to know about a loop -/

/-- The context for a while loop that an AI needs to generate an invariant.
    This is the serializable "prompt" for the LLM.

    The AI sees:
    - The loop condition (as a function sigma -> Bool)
    - The loop body (as an L1 monad)
    - The precondition (what holds before the loop)
    - The postcondition (what must hold after the loop)
    - A human-readable label for identification -/
structure LoopContext (σ : Type) where
  /-- Loop condition -/
  cond : σ → Bool
  /-- Loop body -/
  body : L1Monad σ
  /-- Precondition: what holds before the loop starts -/
  pre : σ → Prop
  /-- Postcondition: what must hold after the loop exits -/
  post : Except Unit Unit → σ → Prop
  /-- Human-readable label for the loop (function name, line number, etc.) -/
  label : String

/-! # Verification condition checking -/

/-- The three verification conditions for a loop invariant.
    Given loop `while cond body` with invariant I:

    VC1 (initialization): precondition implies invariant
    VC2 (preservation): invariant + cond implies body preserves invariant
    VC3 (exit): invariant + not cond implies postcondition

    All three must hold for the invariant to be valid. -/
structure InvariantVCs (σ : Type) where
  /-- VC1: precondition implies invariant -/
  initiation : Prop
  /-- VC2: invariant is preserved by one loop iteration (body does not fail,
      ok results preserve invariant, error results satisfy postcondition) -/
  preservation : Prop
  /-- VC3: invariant + loop exit implies postcondition -/
  exit : Prop

/-- Compute the verification conditions for a loop invariant.
    These match the structure required by wp_while_sound. -/
def computeVCs {σ : Type} (ctx : LoopContext σ) (inv : σ → Prop) : InvariantVCs σ where
  initiation :=
    ∀ s, ctx.pre s → inv s
  preservation :=
    ∀ s, inv s → ctx.cond s = true →
      ¬(ctx.body s).failed ∧
      ∀ r s', (r, s') ∈ (ctx.body s).results →
        match r with
        | Except.ok () => inv s'
        | Except.error () => ctx.post (Except.error ()) s'
  exit :=
    ∀ s, inv s → ctx.cond s = false → ctx.post (Except.ok ()) s

/-- An invariant is valid when all three VCs hold. -/
def invariantValid {σ : Type} (vcs : InvariantVCs σ) : Prop :=
  vcs.initiation ∧ vcs.preservation ∧ vcs.exit

/-! # InvariantOracle: the AI interface -/

/-- An invariant oracle generates suggestions for loop invariants.
    This is the interface that can be backed by:
    - A mock (hard-coded invariants for known loops)
    - A file-based LLM call
    - A direct API call to an LLM

    The oracle is UNTRUSTED. Its output is always kernel-checked.
    Multiple suggestions can be returned for retry logic. -/
structure InvariantOracle (σ : Type) where
  /-- Generate invariant suggestions for a loop context.
      Returns a list of candidates ordered by confidence. -/
  suggest : LoopContext σ → List (InvariantSuggestion σ)

/-! # Mock oracle: hard-coded invariants for known loops -/

/-- A mock oracle that returns hard-coded invariants based on the loop label.
    This demonstrates the architecture without requiring a live LLM.
    Each entry maps a label to a list of candidate invariants. -/
def mkMockOracle {σ : Type} (entries : List (String × List (InvariantSuggestion σ))) :
    InvariantOracle σ where
  suggest := fun ctx =>
    match entries.find? (fun e => e.1 == ctx.label) with
    | some (_, suggestions) => suggestions
    | none => []

/-! # Soundness: the main payoff theorem

This is the critical theorem: if the three VCs hold for a loop invariant,
then the while loop satisfies validHoare {pre} while cond body {post}.

This works by induction on the WhileResult/WhileFail inductives that
define L1.while semantics. The proof structure mirrors wp_while_sound
but with a simpler interface (direct VCs instead of wp transformers). -/

/-- Direct Hoare rule for L1.while using invariant VCs.
    This is the bridge between AI-generated invariants and kernel-checked proofs.

    Given:
    - inv : sigma -> Prop (the invariant, potentially from an LLM)
    - h_init : pre implies inv
    - h_pres : inv + cond implies body preserves inv (and error -> post)
    - h_exit : inv + not cond implies post

    Conclude: validHoare pre (L1.while cond body) post -/
theorem while_invariant_rule {σ : Type}
    (cond : σ → Bool) (body : L1Monad σ)
    (pre : σ → Prop) (post : Except Unit Unit → σ → Prop)
    (inv : σ → Prop)
    (h_init : ∀ s, pre s → inv s)
    (h_pres : ∀ s, inv s → cond s = true →
      ¬(body s).failed ∧
      ∀ r s', (r, s') ∈ (body s).results →
        match r with
        | Except.ok () => inv s'
        | Except.error () => post (Except.error ()) s')
    (h_exit : ∀ s, inv s → cond s = false → post (Except.ok ()) s) :
    validHoare pre (L1.while cond body) post := by
  intro s₀ h_pre
  have h_inv₀ := h_init s₀ h_pre
  -- Prove from inv at any reachable state
  suffices aux : ∀ s, inv s →
      ¬(L1.while cond body s).failed ∧
      ∀ r s₁, (r, s₁) ∈ (L1.while cond body s).results → post r s₁ from
    aux s₀ h_inv₀
  intro s h_inv_s
  constructor
  · -- No failure: induction on WhileFail
    intro hf
    suffices ∀ s', L1.WhileFail cond body s' → inv s' → False from
      this s hf h_inv_s
    intro s' hf'
    induction hf'
    case here s_cur hc hf_body =>
      intro h_inv'
      exact (h_pres s_cur h_inv' hc).1 hf_body
    case later s_cur s_next hc h_ok _h_rest ih =>
      intro h_inv'
      have ⟨_, h_post⟩ := h_pres s_cur h_inv' hc
      exact ih (h_post (Except.ok ()) s_next h_ok)
  · -- Postcondition: induction on WhileResult
    intro r s₁ h_mem
    suffices ∀ s' (p : Except Unit Unit × σ), L1.WhileResult cond body s' p →
        inv s' → post p.1 p.2 from
      this s (r, s₁) h_mem h_inv_s
    intro s' p hr
    induction hr
    case done s_cur hc =>
      intro h_inv'; exact h_exit s_cur h_inv' hc
    case step s_cur s_next p' hc h_ok _h_rest ih =>
      intro h_inv'
      have ⟨_, h_post⟩ := h_pres s_cur h_inv' hc
      exact ih (h_post (Except.ok ()) s_next h_ok)
    case abrupt s_cur s_exit hc h_err =>
      intro h_inv'
      have ⟨_, h_post⟩ := h_pres s_cur h_inv' hc
      exact h_post (Except.error ()) s_exit h_err

/-- Convenience: prove the while loop correct from a valid invariant.
    Bundles the VC computation with the Hoare rule. -/
theorem invariant_gives_hoare {σ : Type}
    (ctx : LoopContext σ) (inv : σ → Prop)
    (h_valid : invariantValid (computeVCs ctx inv)) :
    validHoare ctx.pre (L1.while ctx.cond ctx.body) ctx.post :=
  let ⟨h_init, h_pres, h_exit⟩ := h_valid
  while_invariant_rule ctx.cond ctx.body ctx.pre ctx.post inv h_init h_pres h_exit

/-! # Metrics tracking -/

/-- Track AI invariant generation metrics. -/
structure AIMetrics where
  /-- Total suggestions attempted -/
  totalAttempts : Nat
  /-- Suggestions accepted by kernel -/
  accepted : Nat
  /-- Suggestions rejected -/
  rejected : Nat

/-- Success rate as a percentage. -/
def AIMetrics.successRate (m : AIMetrics) : Float :=
  if m.totalAttempts == 0 then 0.0
  else Float.ofNat m.accepted / Float.ofNat m.totalAttempts * 100.0

/-- Pretty-print metrics. -/
def AIMetrics.toString (m : AIMetrics) : String :=
  s!"AI Metrics: {m.accepted}/{m.totalAttempts} accepted ({m.successRate}%)"

instance : ToString AIMetrics := ⟨AIMetrics.toString⟩

/-! # Documentation

## How to add new oracle entries

To add a new loop invariant to the mock oracle:

1. Identify the loop in the L1 monadic code
2. Write the invariant as (sigma -> Prop)
3. Add an entry to the mock oracle with the loop label
4. Prove the three VCs
5. Use invariant_gives_hoare to get the Hoare triple

## For real LLM integration

1. Serialize LoopContext to a prompt string
2. Call the LLM API
3. Parse the response as a Lean expression
4. Wrap in InvariantSuggestion
5. Attempt to prove the VCs (either via tactic or decision procedure)
6. If VCs fail, feed the error back and retry (up to N times)

The key insight: step 5 is where soundness lives. The LLM can be
arbitrarily wrong, and the kernel will catch it.
-/
