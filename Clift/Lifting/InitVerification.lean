-- InitVerification: System initialization verification framework
--
-- Task 0172: Define InitSpec and boot_correct for proving that
-- initialization code establishes system invariants.
--
-- Problem: All our Hoare triples assume invariants hold. But who
-- establishes them? The init/main function runs ONCE at boot and
-- must set up the state so all invariants are satisfied.
--
-- Key types:
-- - InitSpec: what invariants must hold after boot
-- - boot_correct: if init runs to completion, all invariants established
-- - Composed theorem: init + operations = full system correctness
--
-- Reference: seL4 proved that capDL initialization sets up a correct
-- initial state satisfying all global invariants.

import Clift.Lifting.GlobalInvariant
import Clift.Lifting.AbstractSpec
import Clift.Lifting.FuncSpec

/-! # InitSpec: initialization specification -/

/-- An initialization specification: describes what must hold after
    the system's init function completes.

    The init function runs from a "raw" state (hardware reset, zeroed
    memory, etc.) and must establish all invariants that subsequent
    operations depend on. -/
structure InitSpec (σ : Type) where
  /-- Precondition on the raw initial state (hardware reset state).
      Typically very weak: memory is zeroed, registers have reset values.
      This is part of the TCB — we assume the hardware starts here. -/
  rawState : σ → Prop
  /-- All invariants that must hold after initialization.
      This is the conjunction of all global invariants from the system. -/
  postInvariants : σ → Prop
  /-- Any additional postconditions beyond invariants
      (e.g., specific register values, initial data structure contents). -/
  postConditions : σ → Prop

/-! # Boot correctness -/

/-- The init function is correct: starting from a raw hardware state,
    running init to completion establishes all invariants.

    This is a validHoare triple with:
    - Pre: raw hardware state
    - Post: all invariants + specific postconditions hold -/
def boot_correct {σ : Type}
    (spec : InitSpec σ) (initBody : L1Monad σ) : Prop :=
  validHoare
    spec.rawState
    initBody
    (fun r s => r = Except.ok () → spec.postInvariants s ∧ spec.postConditions s)

/-- Stronger form: init must succeed (no failure, no exception). -/
def boot_correct_total {σ : Type}
    (spec : InitSpec σ) (initBody : L1Monad σ) : Prop :=
  validHoare
    spec.rawState
    initBody
    (fun r s =>
      r = Except.ok () ∧
      spec.postInvariants s ∧
      spec.postConditions s)

/-! # Composition: init + operations = full system correctness -/

/-- System correctness: if init is correct and all operations preserve
    invariants, then after init followed by any sequence of operations,
    the invariants still hold.

    This is the top-level theorem that connects:
    1. boot_correct (init establishes invariants)
    2. systemInvariant (all operations preserve invariants)
    => After init + any operations, invariants hold.

    This is the most important theorem in a verification project. -/
structure SystemCorrectness (σ : Type) where
  /-- Init spec -/
  initSpec : InitSpec σ
  /-- Init function body (L1 lifted) -/
  initBody : L1Monad σ
  /-- Procedure environment for operational functions -/
  l1Env : L1.L1ProcEnv σ
  /-- Global invariant -/
  inv : GlobalInvariant σ
  /-- Proof: init establishes invariants -/
  init_correct : boot_correct initSpec initBody
  /-- Proof: invariants imply the init spec's postInvariants -/
  inv_is_postInv : ∀ s, inv s → initSpec.postInvariants s
  /-- Proof: init establishes the global invariant -/
  init_establishes_inv : validHoare initSpec.rawState initBody
    (fun r s => r = Except.ok () → inv s)
  /-- Proof: all operations preserve the invariant -/
  ops_preserve : systemInvariant l1Env inv

/-- The main theorem: after init + any operation call, invariant holds. -/
theorem system_correct_call {σ : Type}
    (sys : SystemCorrectness σ)
    (s₀ : σ) (h_raw : sys.initSpec.rawState s₀)
    (s₁ : σ) (h_init : (Except.ok (), s₁) ∈ (sys.initBody s₀).results)
    (name : ProcName) (body : L1Monad σ)
    (h_lookup : sys.l1Env name = some body) :
    -- After init succeeded, calling any operation preserves invariant
    ∀ rv s₂, (rv, s₂) ∈ (body s₁).results → sys.inv s₂ := by
  -- Init establishes the invariant
  have h_inv : sys.inv s₁ := by
    have ⟨_, h_post⟩ := sys.init_establishes_inv s₀ h_raw
    exact h_post (Except.ok ()) s₁ h_init rfl
  -- The operation preserves it
  intro rv s₂ h_mem
  have h_pres := sys.ops_preserve name body h_lookup
  have ⟨_, h_post⟩ := h_pres s₁ h_inv
  exact h_post rv s₂ h_mem

/-! # Example: ring buffer init establishes rbInvariant -/

namespace InitExample

/-- Ring buffer state (simplified). -/
structure RBState where
  head : Nat
  tail : Nat
  count : Nat
  capacity : Nat
  initialized : Bool

/-- Ring buffer invariant: count <= capacity, capacity > 0. -/
def rbInvariant : GlobalInvariant RBState :=
  fun s => s.count ≤ s.capacity ∧ s.capacity > 0 ∧ s.initialized = true

/-- Raw state: hardware reset (everything zeroed). -/
def rbRawState : RBState → Prop :=
  fun s => s.head = 0 ∧ s.tail = 0 ∧ s.count = 0 ∧ s.capacity = 0 ∧ s.initialized = false

/-- Init function: set capacity to 16, mark as initialized. -/
def rbInit : L1Monad RBState :=
  fun _s =>
    { results := {(Except.ok (), {
        head := 0, tail := 0, count := 0, capacity := 16, initialized := true
      })}
      failed := False }

/-- Init spec for ring buffer. -/
def rbInitSpec : InitSpec RBState where
  rawState := rbRawState
  postInvariants := rbInvariant
  postConditions := fun s => s.capacity = 16 ∧ s.count = 0

/-- Ring buffer init is correct: establishes the invariant. -/
theorem rbInit_correct : boot_correct rbInitSpec rbInit := by
  intro s₀ h_raw
  constructor
  · intro hf; exact hf
  · intro r s₁ h_mem _h_ok
    simp [rbInit] at h_mem
    obtain ⟨rfl, rfl⟩ := h_mem
    constructor
    · -- postInvariants (rbInvariant)
      refine ⟨?_, ?_, rfl⟩ <;> simp
    · -- postConditions
      exact ⟨rfl, rfl⟩

/-- Init establishes the global invariant. -/
theorem rbInit_establishes_inv :
    validHoare rbRawState rbInit (fun r s => r = Except.ok () → rbInvariant s) := by
  intro s₀ h_raw
  constructor
  · intro hf; exact hf
  · intro r s₁ h_mem h_ok
    simp [rbInit] at h_mem
    obtain ⟨rfl, rfl⟩ := h_mem
    refine ⟨?_, ?_, rfl⟩ <;> simp

/-- Example write operation that preserves the invariant. -/
def rbWrite : L1Monad RBState :=
  fun s =>
    if s.count < s.capacity then
      { results := {(Except.ok (), { s with
          tail := (s.tail + 1) % s.capacity
          count := s.count + 1 })}
        failed := False }
    else
      { results := {(Except.error (), s)}
        failed := False }

/-- Write preserves the invariant. -/
theorem rbWrite_preserves : preserves_invariant_unconditional rbInvariant rbWrite := by
  intro s₀ ⟨h_cnt, h_cap, h_init⟩
  unfold rbWrite
  split
  case isTrue h =>
    constructor
    · intro hf; exact hf
    · intro r s₁ h_mem
      simp at h_mem
      obtain ⟨rfl, rfl⟩ := h_mem
      refine ⟨?_, h_cap, h_init⟩; simp; omega
  case isFalse h =>
    constructor
    · intro hf; exact hf
    · intro r s₁ h_mem
      simp at h_mem
      obtain ⟨rfl, rfl⟩ := h_mem
      exact ⟨h_cnt, h_cap, h_init⟩

end InitExample

/-! # Documentation

## How to verify initialization code

1. **Define the raw state predicate**: what does the hardware look like
   at reset? Typically: memory is zeroed, registers have reset values.
   This is part of the TCB.

2. **Define the InitSpec**: what invariants must hold after init, and
   any specific postconditions (e.g., data structure sizes).

3. **Import and lift the init function**: use the CImporter to get the
   CSimpl term, then lift to L1.

4. **Prove boot_correct**: show that starting from rawState, init
   establishes all postInvariants and postConditions.

5. **Assemble SystemCorrectness**: combine init_correct with
   ops_preserve (from your per-function invariant proofs) to get
   the full system correctness theorem.

## Common pitfalls

- **Missing rawState assumptions**: if the hardware doesn't actually
  zero memory on reset, your rawState predicate is wrong and proofs
  are vacuously true.

- **Init uses heap operations**: if init mallocs or writes to the heap,
  you need heap validity in the raw state. Consider whether the heap
  allocator itself needs initialization.

- **Multiple init functions**: some systems have a chain of init
  functions (hardware init -> OS init -> app init). Model each as
  a separate InitSpec and compose them sequentially.

## What enters the TCB

- The `rawState` predicate is in the TCB: we trust that the hardware
  actually starts in this state.
- Everything else (init body, invariants, proofs) is verified.
-/
