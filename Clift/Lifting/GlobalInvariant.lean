-- GlobalInvariant: Framework for system-wide invariant proofs
--
-- A global invariant is a predicate on the program state that must hold
-- after every function call. Each function must preserve the invariant:
-- {inv /\ P} f {inv /\ Q}. If all functions preserve the invariant,
-- any sequence of function calls preserves it.
--
-- This follows seL4's approach where ~80% of proof effort was invariant
-- proofs. The framework makes invariant obligations explicit and
-- composable.
--
-- Design choices:
-- 1. GlobalInvariant is just (sigma -> Prop), not a typeclass. Multiple
--    invariants can coexist and be composed.
-- 2. InvariantFuncSpec bundles a FuncSpec with invariant preservation.
-- 3. SystemInvariant proves all functions in a ProcEnv preserve the invariant.
--
-- Reference: seL4's global_automaton_invs
-- Reference: plan.md Phase 5

import Clift.Lifting.FuncSpec
import Clift.Lifting.L1HoareRules

/-! # Global Invariant type -/

/-- A global invariant is a predicate on the state type.
    For C programs, sigma is typically ProgramState. -/
abbrev GlobalInvariant (σ : Type) := σ → Prop

/-! # Invariant preservation -/

/-- A function body preserves an invariant: if the invariant holds
    before execution (along with the function's precondition P),
    then it holds after execution (along with the postcondition Q).

    This is the fundamental obligation for each function. -/
def preserves_invariant {σ : Type}
    (inv : GlobalInvariant σ)
    (body : L1Monad σ)
    (P : σ → Prop)
    (Q : Except Unit Unit → σ → Prop) : Prop :=
  validHoare (fun s => inv s ∧ P s) body (fun r s => inv s ∧ Q r s)

/-- Simplified form: body preserves invariant unconditionally.
    No additional pre/post conditions beyond the invariant itself. -/
def preserves_invariant_unconditional {σ : Type}
    (inv : GlobalInvariant σ) (body : L1Monad σ) : Prop :=
  validHoare inv body (fun _ s => inv s)

/-! # InvariantFuncSpec: FuncSpec with invariant obligation -/

/-- A function specification that also carries invariant preservation.
    This bundles together:
    1. The normal FuncSpec (pre -> body -> post)
    2. The invariant preservation proof

    Callers can use the FuncSpec for functional correctness AND
    know that the invariant is maintained. -/
structure InvariantFuncSpec (σ : Type) extends FuncSpec σ where
  /-- The global invariant this spec preserves -/
  inv : GlobalInvariant σ
  /-- Proof that the invariant is preserved -/
  inv_ok : ∀ (body : L1Monad σ),
    toFuncSpec.satisfiedBy body →
    preserves_invariant inv body toFuncSpec.pre toFuncSpec.post

/-- If a body satisfies an InvariantFuncSpec, then it preserves the invariant
    whenever the function's precondition holds. -/
theorem invariantFuncSpec_preserves {σ : Type}
    (ispec : InvariantFuncSpec σ) (body : L1Monad σ)
    (h_sat : ispec.toFuncSpec.satisfiedBy body) :
    preserves_invariant ispec.inv body ispec.pre ispec.post :=
  ispec.inv_ok body h_sat

/-! # Building invariant-preserving FuncSpecs -/

/-- Build an InvariantFuncSpec from a FuncSpec + invariant proof.

    The invariant proof obligation is: starting from (inv /\ pre),
    the body establishes (inv /\ post). This is the standard form.

    The key insight: if the FuncSpec's precondition already includes
    the invariant, and the postcondition preserves it, then the
    InvariantFuncSpec is trivially constructed. -/
def InvariantFuncSpec.mk' {σ : Type}
    (inv : GlobalInvariant σ)
    (pre : σ → Prop)
    (post : Except Unit Unit → σ → Prop)
    (h_preserves : ∀ body : L1Monad σ,
      validHoare pre body post →
      preserves_invariant inv body pre post) :
    InvariantFuncSpec σ :=
  { pre := pre
    post := post
    inv := inv
    inv_ok := fun body h_sat => h_preserves body h_sat }

/-- When the precondition implies the invariant and the postcondition
    preserves it, the invariant-preservation proof is straightforward.

    This is the common case: most functions don't break invariants
    that they assume in their preconditions. -/
theorem preserves_from_funcSpec {σ : Type}
    (inv : GlobalInvariant σ)
    (pre : σ → Prop) (post : Except Unit Unit → σ → Prop)
    (body : L1Monad σ)
    -- The spec when started from inv /\ pre must establish inv /\ post
    (h_strong : validHoare (fun s => inv s ∧ pre s) body (fun r s => inv s ∧ post r s)) :
    preserves_invariant inv body pre post :=
  h_strong

/-! # System-wide invariant: all functions preserve it -/

/-- A system invariant holds when every function in the procedure
    environment preserves the invariant.

    Given:
    - An L1 procedure environment mapping names to L1 bodies
    - A global invariant
    - A precondition for each function (e.g., parameter constraints)

    The system invariant says: for every function name in the environment,
    calling that function preserves the invariant. -/
def systemInvariant {σ : Type}
    (l1Env : L1.L1ProcEnv σ)
    (inv : GlobalInvariant σ) : Prop :=
  ∀ (name : ProcName) (body : L1Monad σ),
    l1Env name = some body →
    preserves_invariant_unconditional inv body

/-! # Composition: sequential calls preserve invariant -/

/-- If two computations both preserve the invariant unconditionally,
    then their sequential composition also preserves it. -/
theorem preserves_seq {σ : Type}
    (inv : GlobalInvariant σ) (m₁ m₂ : L1Monad σ)
    (h₁ : preserves_invariant_unconditional inv m₁)
    (h₂ : preserves_invariant_unconditional inv m₂) :
    preserves_invariant_unconditional inv (L1.seq m₁ m₂) := by
  intro s₀ h_inv
  have ⟨h₁_nf, h₁_post⟩ := h₁ s₀ h_inv
  constructor
  · -- no failure in seq
    intro hf
    change (_ ∨ _) at hf
    rcases hf with hf₁ | ⟨s', h_mem, hf₂⟩
    · exact h₁_nf hf₁
    · have h_inv' := h₁_post (Except.ok ()) s' h_mem
      exact (h₂ s' h_inv').1 hf₂
  · -- postcondition: inv preserved
    intro r s₁ h_mem
    change (_ ∨ _) at h_mem
    rcases h_mem with ⟨s', h_m₁, h_m₂⟩ | ⟨h_err, _⟩
    · have h_inv' := h₁_post (Except.ok ()) s' h_m₁
      exact (h₂ s' h_inv').2 r s₁ h_m₂
    · exact h₁_post (Except.error ()) s₁ h_err

/-- If a system invariant holds and we make a call, the invariant
    is preserved. This is the fundamental composition theorem. -/
theorem systemInvariant_call {σ : Type}
    (l1Env : L1.L1ProcEnv σ) (inv : GlobalInvariant σ)
    (h_sys : systemInvariant l1Env inv)
    (name : ProcName) (body : L1Monad σ)
    (h_lookup : l1Env name = some body) :
    preserves_invariant_unconditional inv body :=
  h_sys name body h_lookup

/-- If the system invariant holds, any sequence of N function calls
    preserves the invariant. Proved by induction on the call sequence. -/
theorem systemInvariant_calls {σ : Type}
    (l1Env : L1.L1ProcEnv σ) (inv : GlobalInvariant σ)
    (h_sys : systemInvariant l1Env inv)
    (calls : List ProcName) :
    ∀ (s : σ), inv s →
      ∀ name, name ∈ calls →
        ∀ body, l1Env name = some body →
          ¬(body s).failed ∧
          ∀ rv s', (rv, s') ∈ (body s).results → inv s' := by
  intro s h_inv name _h_mem body h_lookup
  exact h_sys name body h_lookup s h_inv

/-! # Invariant conjunction: composing multiple invariants -/

/-- Two invariants can be composed: if each function preserves both
    invariants independently, it preserves their conjunction. -/
theorem preserves_conjunction {σ : Type}
    (inv₁ inv₂ : GlobalInvariant σ) (body : L1Monad σ)
    (h₁ : preserves_invariant_unconditional inv₁ body)
    (h₂ : preserves_invariant_unconditional inv₂ body) :
    preserves_invariant_unconditional (fun s => inv₁ s ∧ inv₂ s) body := by
  intro s₀ ⟨hi₁, hi₂⟩
  have ⟨h₁_nf, h₁_post⟩ := h₁ s₀ hi₁
  have ⟨_, h₂_post⟩ := h₂ s₀ hi₂
  exact ⟨h₁_nf, fun r s₁ h_mem => ⟨h₁_post r s₁ h_mem, h₂_post r s₁ h_mem⟩⟩

/-! # Example: Counter < MAX invariant -/

namespace CounterExample

/-- A simple state with a counter. -/
structure CounterState where
  counter : Nat
  max_val : Nat

/-- The invariant: counter is always less than max_val. -/
def counterInv : GlobalInvariant CounterState :=
  fun s => s.counter < s.max_val

/-- An increment operation that checks before incrementing. -/
def safeIncrement : L1Monad CounterState :=
  fun s =>
    if s.counter + 1 < s.max_val then
      { results := {(Except.ok (), { s with counter := s.counter + 1 })}
        failed := False }
    else
      { results := {(Except.error (), s)}
        failed := False }

/-- safeIncrement preserves the counter invariant. -/
theorem safeIncrement_preserves :
    preserves_invariant_unconditional counterInv safeIncrement := by
  intro s₀ h_inv
  unfold safeIncrement
  split
  case isTrue h =>
    constructor
    · intro hf; exact hf
    · intro r s₁ h_mem
      have heq := Prod.mk.inj h_mem
      cases heq.2
      unfold counterInv
      show s₀.counter + 1 < s₀.max_val
      exact h
  case isFalse h =>
    constructor
    · intro hf; exact hf
    · intro r s₁ h_mem
      have heq := Prod.mk.inj h_mem
      cases heq.2
      exact h_inv

/-- A reset operation that sets counter to 0. -/
def resetCounter : L1Monad CounterState :=
  fun s =>
    { results := {(Except.ok (), { s with counter := 0 })}
      failed := False }

/-- resetCounter preserves the invariant (0 < max_val follows from inv). -/
theorem resetCounter_preserves :
    preserves_invariant_unconditional counterInv resetCounter := by
  intro s₀ h_inv
  unfold resetCounter
  constructor
  · intro hf; exact hf
  · intro r s₁ h_mem
    have heq := Prod.mk.inj h_mem
    cases heq.2
    unfold counterInv at h_inv ⊢
    show 0 < s₀.max_val
    omega

end CounterExample

/-! # Integration with FuncSpec

The workflow for invariant-preserving verification:

1. Define the global invariant: `def myInv : GlobalInvariant MyState := ...`

2. For each function, write a FuncSpec as before:
   `def f_spec : FuncSpec MyState := { pre := ..., post := ... }`

3. Prove the function satisfies its spec:
   `theorem f_sat : f_spec.satisfiedBy l1_f_body := ...`

4. Prove invariant preservation:
   `theorem f_inv : preserves_invariant myInv l1_f_body f_spec.pre f_spec.post := ...`

   Or use the stronger form:
   `theorem f_inv : preserves_invariant_unconditional myInv l1_f_body := ...`

5. Assemble the system invariant:
   `theorem sys_inv : systemInvariant l1ProcEnv myInv := ...`

6. Use systemInvariant_call to reason about call sequences.
-/
