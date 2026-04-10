-- Noninterference: Information Flow Security
--
-- The gold standard for confidentiality: noninterference.
-- If two initial states agree on LOW-observable data, then after any
-- sequence of operations, they still agree on LOW-observable data.
--
-- seL4 proved noninterference for the entire kernel (storage channels only,
-- not timing channels). This module defines the framework; full kernel-scale
-- proofs are Phase K work.
--
-- Design choices:
-- 1. Security domains are classified as HIGH or LOW per state component.
-- 2. Indistinguishability is an equivalence relation parameterized by domain.
-- 3. Noninterference is stated as a trace property: for any sequence of
--    operations, LOW-equivalent initial states produce LOW-equivalent final states.
-- 4. We provide the unwinding conditions (step consistency, output consistency,
--    locally respects) that are sufficient for noninterference.
--
-- Reference: seL4 TOCS 2014, Section 6.3 (noninterference)
-- Reference: Goguen & Meseguer, "Security Policies and Security Models", 1982
-- Reference: Rushby, "Noninterference, Transitivity, and Channel-Control Security Policies", 1992

import Clift.Lifting.AbstractSpec

/-! # Security Level Classification -/

/-- Security levels. We use a simple two-level lattice (HIGH/LOW) following
    the standard Bell-LaPadula / noninterference literature.

    Extension to multi-level security (a general lattice) is straightforward
    but adds complexity without changing the framework shape. -/
inductive SecurityLevel where
  | low
  | high
  deriving DecidableEq, Repr

/-- LOW can flow to HIGH, but HIGH cannot flow to LOW. -/
def SecurityLevel.flowsTo : SecurityLevel → SecurityLevel → Bool
  | .low, _ => true
  | .high, .high => true
  | .high, .low => false

/-! # Indistinguishability -/

/-- A domain classification assigns a security level to each "component"
    of the abstract state. The component type C is abstract -- it could be
    field names, memory regions, or any other decomposition.

    Example: for a ring buffer, components might be {data, count, capacity}
    where data is HIGH and count/capacity are LOW. -/
structure DomainClassification (Component : Type) where
  level : Component → SecurityLevel

/-- Indistinguishability relation: two states are indistinguishable at level l
    if they agree on all components classified at or below level l.

    This is parameterized by a projection function that extracts the value
    of a component from the state. -/
def indistinguishable {S Component V : Type}
    (classify : DomainClassification Component)
    (project : Component → S → V)
    (l : SecurityLevel) (s₁ s₂ : S) : Prop :=
  ∀ (c : Component),
    classify.level c = .low ∨ (classify.level c = .high ∧ l = .high) →
    project c s₁ = project c s₂

/-- LOW-indistinguishability: states agree on all LOW components.
    This is the most common case (what can a LOW observer see?). -/
def lowIndistinguishable {S Component V : Type}
    (classify : DomainClassification Component)
    (project : Component → S → V)
    (s₁ s₂ : S) : Prop :=
  ∀ (c : Component), classify.level c = .low → project c s₁ = project c s₂

/-- LOW-indistinguishability is an equivalence relation. -/
theorem lowIndistinguishable_refl {S Component V : Type}
    (classify : DomainClassification Component)
    (project : Component → S → V) :
    ∀ s : S, lowIndistinguishable classify project s s := by
  intro s c _; rfl

theorem lowIndistinguishable_symm {S Component V : Type}
    (classify : DomainClassification Component)
    (project : Component → S → V) :
    ∀ s₁ s₂ : S, lowIndistinguishable classify project s₁ s₂ →
      lowIndistinguishable classify project s₂ s₁ := by
  intro s₁ s₂ h c h_low; exact (h c h_low).symm

theorem lowIndistinguishable_trans {S Component V : Type}
    (classify : DomainClassification Component)
    (project : Component → S → V) :
    ∀ s₁ s₂ s₃ : S,
      lowIndistinguishable classify project s₁ s₂ →
      lowIndistinguishable classify project s₂ s₃ →
      lowIndistinguishable classify project s₁ s₃ := by
  intro s₁ s₂ s₃ h₁₂ h₂₃ c h_low
  exact (h₁₂ c h_low).trans (h₂₃ c h_low)

/-! # Noninterference -/

/-- Single-step noninterference (unwinding condition):
    if two states are LOW-indistinguishable before a LOW operation,
    they remain LOW-indistinguishable after.

    "LOW operation" = an operation whose effects should be visible to LOW.
    "HIGH operation" = an operation that may touch HIGH data. For HIGH
    operations, we need a separate condition (step consistency). -/
def stepConsistentLow {S Component V : Type} {Op : Type}
    (spec : AbstractSpec S Op)
    (classify : DomainClassification Component)
    (project : Component → S → V)
    (opLevel : Op → SecurityLevel) : Prop :=
  ∀ (op : Op) (s₁ s₂ s₁' s₂' : S),
    opLevel op = .low →
    spec.inv s₁ → spec.inv s₂ →
    (spec.opSpec op).pre s₁ → (spec.opSpec op).pre s₂ →
    (spec.opSpec op).post s₁ s₁' → (spec.opSpec op).post s₂ s₂' →
    lowIndistinguishable classify project s₁ s₂ →
    lowIndistinguishable classify project s₁' s₂'

/-- HIGH operations don't affect LOW-observable state.
    This is the "locally respects" unwinding condition:
    a HIGH operation cannot change what a LOW observer sees. -/
def locallyRespects {S Component V : Type} {Op : Type}
    (spec : AbstractSpec S Op)
    (classify : DomainClassification Component)
    (project : Component → S → V)
    (opLevel : Op → SecurityLevel) : Prop :=
  ∀ (op : Op) (s s' : S),
    opLevel op = .high →
    spec.inv s →
    (spec.opSpec op).pre s →
    (spec.opSpec op).post s s' →
    lowIndistinguishable classify project s s'

-- Output consistency: LOW-indistinguishable states produce
-- LOW-indistinguishable outputs for LOW operations.
-- (For our framework where outputs are captured in the post-state,
-- this is subsumed by stepConsistentLow.)

/-- Noninterference for a single step: combines step consistency and
    locally respects. If both hold, then for ANY operation (LOW or HIGH),
    LOW-indistinguishable inputs produce LOW-indistinguishable outputs. -/
theorem singleStepNoninterference {S Component V : Type} {Op : Type}
    (spec : AbstractSpec S Op)
    (classify : DomainClassification Component)
    (project : Component → S → V)
    (opLevel : Op → SecurityLevel)
    (h_step : stepConsistentLow spec classify project opLevel)
    (h_local : locallyRespects spec classify project opLevel)
    (op : Op) (s₁ s₂ s₁' s₂' : S)
    (h_inv₁ : spec.inv s₁) (h_inv₂ : spec.inv s₂)
    (h_pre₁ : (spec.opSpec op).pre s₁) (h_pre₂ : (spec.opSpec op).pre s₂)
    (h_post₁ : (spec.opSpec op).post s₁ s₁') (h_post₂ : (spec.opSpec op).post s₂ s₂')
    (h_equiv : lowIndistinguishable classify project s₁ s₂) :
    lowIndistinguishable classify project s₁' s₂' := by
  cases h_level : opLevel op with
  | low =>
    exact h_step op s₁ s₂ s₁' s₂' h_level h_inv₁ h_inv₂ h_pre₁ h_pre₂ h_post₁ h_post₂ h_equiv
  | high =>
    -- HIGH op: s₁ ~ s₁' and s₂ ~ s₂' (locally respects), and s₁ ~ s₂ (assumption)
    -- By transitivity: s₁' ~ s₁ ~ s₂ ~ s₂'
    have h₁ := h_local op s₁ s₁' h_level h_inv₁ h_pre₁ h_post₁
    have h₂ := h_local op s₂ s₂' h_level h_inv₂ h_pre₂ h_post₂
    exact lowIndistinguishable_trans classify project s₁' s₁ s₂'
      (lowIndistinguishable_symm classify project s₁ s₁' h₁)
      (lowIndistinguishable_trans classify project s₁ s₂ s₂' h_equiv h₂)

/-! # Noninterference Transfer via Refinement -/

/-- If the abstract spec satisfies noninterference (via unwinding conditions),
    and the C implementation refines the abstract spec, then the concrete
    system also satisfies noninterference (at the abstract level).

    The concrete states map to abstract states via the simulation relation R,
    and security holds on those abstract projections.

    This theorem shape shows that noninterference composes with refinement.
    The full proof would require showing that refinement preserves the
    unwinding conditions step by step. -/
theorem noninterference_transfers {S C Component V : Type} {Op : Type}
    {spec : AbstractSpec S Op}
    {impl : Op → L1Monad C}
    {R : SimRel S C}
    (classify : DomainClassification Component)
    (project : Component → S → V)
    (opLevel : Op → SecurityLevel)
    (h_refines : ∀ op, opRefinementTotal (spec.opSpec op) (impl op) R)
    (h_step : stepConsistentLow spec classify project opLevel)
    (h_local : locallyRespects spec classify project opLevel) :
    -- For any operation and any two concrete states whose abstract projections
    -- are LOW-indistinguishable, the concrete results' abstract projections
    -- are also LOW-indistinguishable.
    ∀ (op : Op) (c₁ c₂ : C) (s₁ s₂ : S),
      R c₁ s₁ → R c₂ s₂ →
      spec.inv s₁ → spec.inv s₂ →
      (spec.opSpec op).pre s₁ → (spec.opSpec op).pre s₂ →
      lowIndistinguishable classify project s₁ s₂ →
      ∀ rv₁ c₁' rv₂ c₂',
        (rv₁, c₁') ∈ ((impl op) c₁).results →
        (rv₂, c₂') ∈ ((impl op) c₂).results →
        ∃ s₁' s₂', R c₁' s₁' ∧ R c₂' s₂' ∧
          lowIndistinguishable classify project s₁' s₂' := by
  intro op c₁ c₂ s₁ s₂ h_r₁ h_r₂ h_inv₁ h_inv₂ h_pre₁ h_pre₂ h_equiv
    rv₁ c₁' rv₂ c₂' h_mem₁ h_mem₂
  -- Get abstract post-states from refinement
  have ⟨_, h_post₁⟩ := h_refines op c₁ s₁ h_r₁ h_pre₁
  have ⟨_, h_post₂⟩ := h_refines op c₂ s₂ h_r₂ h_pre₂
  obtain ⟨s₁', h_r₁', h_abs₁⟩ := h_post₁ rv₁ c₁' h_mem₁
  obtain ⟨s₂', h_r₂', h_abs₂⟩ := h_post₂ rv₂ c₂' h_mem₂
  -- Apply single-step noninterference on abstract states
  have h_ni := singleStepNoninterference spec classify project opLevel
    h_step h_local op s₁ s₂ s₁' s₂' h_inv₁ h_inv₂ h_pre₁ h_pre₂ h_abs₁ h_abs₂ h_equiv
  exact ⟨s₁', s₂', h_r₁', h_r₂', h_ni⟩

/-! # Example: Ring Buffer with HIGH Data, LOW Metadata -/

namespace RBNoninterferenceExample

/-- Abstract ring buffer state. -/
structure QueueState where
  elems : List Nat
  size : Nat
  capacity : Nat

/-- State components. -/
inductive QueueComponent where
  | data      -- the actual queue elements (HIGH)
  | size      -- current size (LOW -- publicly observable)
  | capacity  -- max capacity (LOW)

/-- Classification: data is HIGH, metadata is LOW. -/
def rbClassify : DomainClassification QueueComponent where
  level
    | .data => .high
    | .size => .low
    | .capacity => .low

/-- Projection: extract a component's value from the state.
    We use a sum type to handle different value types. -/
def rbProject : QueueComponent → QueueState → (List Nat × Nat)
  | .data, s => (s.elems, 0)
  | .size, s => ([], s.size)
  | .capacity, s => ([], s.capacity)

/-- Queue operations. -/
inductive QueueOp where
  | push (val : Nat)
  | pop
  | size

/-- Operation security levels:
    - push/pop are HIGH (they modify the data)
    - size is LOW (it only reads metadata) -/
def rbOpLevel : QueueOp → SecurityLevel
  | .push _ => .high
  | .pop => .high
  | .size => .low

/-- Abstract spec. -/
def rbSpec : AbstractSpec QueueState QueueOp where
  init := fun s => s.elems = [] ∧ s.size = 0 ∧ s.capacity > 0
  opSpec := fun op => match op with
    | .push val => {
        pre := fun s => s.size < s.capacity
        post := fun s s' => s'.elems = s.elems ++ [val] ∧
                            s'.size = s.size + 1 ∧ s'.capacity = s.capacity
      }
    | .pop => {
        pre := fun s => s.elems ≠ []
        post := fun s s' =>
          ∃ v rest, s.elems = v :: rest ∧ s'.elems = rest ∧
          s'.size = s.size - 1 ∧ s'.capacity = s.capacity
      }
    | .size => {
        pre := fun _ => True
        post := fun s s' => s' = s
      }
  inv := fun s => s.size = s.elems.length ∧ s.size ≤ s.capacity ∧ s.capacity > 0

-- Locally respects: HIGH operations (push/pop) don't change LOW-observable state.
--
-- Limitation: push changes size, which is LOW. So push does NOT locally respect
-- in the strict sense! This is a real modeling issue. In seL4's formulation,
-- the "locally respects" condition is about the executing domain's operations
-- not leaking to other domains. Here push is executed by a HIGH entity but
-- modifies LOW state (size).
--
-- This is actually correct behavior: the SIZE is public metadata that changes
-- when the queue changes. The CONTENT is private. So the right formulation
-- for this system is:
--
-- - Push/pop are MIXED: they modify both HIGH (data) and LOW (size) state
-- - The noninterference property we want: knowing the sequence of push/pop
--   operations (which is public since size changes), an observer can learn
--   the size but NOT the data values
--
-- For the standard unwinding approach to work, we need to classify operations
-- more carefully. Size is a LOW operation. Push/pop have LOW-observable
-- side effects (size change) but HIGH data effects.
--
-- This is documented honestly: the simple HIGH/LOW classification doesn't
-- capture the nuance of operations with mixed effects. A more refined
-- framework would use "intransitive noninterference" or "conditioned
-- noninterference" from the literature.

/-- What we CAN prove: size operation preserves LOW-equivalence. -/
theorem size_step_consistent :
    ∀ (s₁ s₂ s₁' s₂' : QueueState),
      rbSpec.inv s₁ → rbSpec.inv s₂ →
      (rbSpec.opSpec .size).pre s₁ → (rbSpec.opSpec .size).pre s₂ →
      (rbSpec.opSpec .size).post s₁ s₁' → (rbSpec.opSpec .size).post s₂ s₂' →
      lowIndistinguishable rbClassify rbProject s₁ s₂ →
      lowIndistinguishable rbClassify rbProject s₁' s₂' := by
  intro s₁ s₂ s₁' s₂' _ _ _ _ h_post₁ h_post₂ h_equiv
  -- size is read-only: s₁' = s₁ and s₂' = s₂
  subst h_post₁; subst h_post₂
  exact h_equiv

/-- Push preserves the HIGH-data noninterference property:
    if two states have the same size and capacity (LOW-equivalent),
    after push, they still have the same size and capacity.

    The data changes, but data is HIGH and not observable by LOW. -/
theorem push_preserves_low_metadata (s₁ s₂ : QueueState) (v₁ v₂ : Nat)
    (s₁' s₂' : QueueState)
    (_h_inv₁ : rbSpec.inv s₁) (_h_inv₂ : rbSpec.inv s₂)
    (_h_pre₁ : (rbSpec.opSpec (.push v₁)).pre s₁)
    (_h_pre₂ : (rbSpec.opSpec (.push v₂)).pre s₂)
    (h_post₁ : (rbSpec.opSpec (.push v₁)).post s₁ s₁')
    (h_post₂ : (rbSpec.opSpec (.push v₂)).post s₂ s₂')
    (h_equiv : lowIndistinguishable rbClassify rbProject s₁ s₂) :
    lowIndistinguishable rbClassify rbProject s₁' s₂' := by
  intro c h_low
  cases c with
  | data => simp [rbClassify] at h_low
  | size =>
    simp [rbProject]
    obtain ⟨_, h_size₁, _⟩ := h_post₁
    obtain ⟨_, h_size₂, _⟩ := h_post₂
    rw [h_size₁, h_size₂]
    have h := h_equiv .size (by simp [rbClassify])
    simp [rbProject] at h
    omega
  | capacity =>
    simp [rbProject]
    obtain ⟨_, _, h_cap₁⟩ := h_post₁
    obtain ⟨_, _, h_cap₂⟩ := h_post₂
    rw [h_cap₁, h_cap₂]
    have h := h_equiv .capacity (by simp [rbClassify])
    simp [rbProject] at h
    exact h

end RBNoninterferenceExample

/-! # Documentation

## Noninterference: What It Means and Its Limits

Noninterference says: a LOW observer cannot distinguish between two system
executions that differ only in HIGH inputs. Concretely:

1. Start with two states that look the same to LOW (same size, capacity)
2. Run any sequence of operations (possibly with different HIGH data)
3. The resulting states still look the same to LOW

### What seL4 proved
seL4 proved noninterference for storage channels (memory, IPC) but NOT
for timing channels. Timing channels require a different analysis
(typically hardware-specific).

### Limitations of the simple model
The example above shows a real limitation: push/pop have MIXED effects
(both HIGH and LOW state changes). The standard unwinding conditions
(stepConsistentLow + locallyRespects) handle this by requiring that
HIGH operations don't change LOW state at all, which is too strict.

For systems with mixed effects, alternatives include:
- Intransitive noninterference (Rushby 1992): allows controlled downgrading
- Conditioned noninterference: security depends on what operations are scheduled
- Declassification: explicitly model when HIGH data becomes LOW

### Recommended approach for Clift users
1. Start with the simple model (this module) for systems with clean separation
2. For systems with mixed effects, use the per-component approach in
   push_preserves_low_metadata (prove each LOW component is preserved)
3. For declassification, define a separate "authorized downgrade" predicate
-/
