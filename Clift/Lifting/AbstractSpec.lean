-- AbstractSpec: Framework for writing abstract specifications separate from C
--
-- An abstract specification describes WHAT a system does, independent of HOW
-- it is implemented in C. This follows seL4's approach where a 4,900-line
-- abstract spec describes kernel behavior, and the C code is proven to refine it.
--
-- Key types:
-- - AbstractSpec: state type + operations + per-operation pre/post
-- - Refinement: C implementation refines abstract spec via a simulation relation
-- - The simulation relation maps concrete state to abstract state
--
-- Design choice: We use a record-based approach (not a typeclass) because:
-- 1. Multiple specs can exist for the same state type
-- 2. Specs are data, not ad-hoc polymorphism
-- 3. Composition is explicit, not inferred
--
-- Reference: seL4's abstract specification (design-spec)
-- Reference: plan.md Phase 5

import Clift.Lifting.FuncSpec
import Clift.Lifting.L1HoareRules

/-! # Abstract Specification -/

/-- An operation specification: precondition and postcondition over abstract state.
    This is the abstract analog of FuncSpec, but over the abstract state type
    rather than the concrete C state. -/
structure OpSpec (S : Type) where
  /-- Precondition on abstract state before the operation -/
  pre : S → Prop
  /-- Postcondition: given initial state, relates return value to final state.
      The return value is modeled as part of the final state for simplicity. -/
  post : S → S → Prop

/-- An abstract specification for a system with state type S and
    operation index type Op. Each operation has a pre/post spec.

    Example: a key-value store has S = (Key -> Option Value) and
    operations {get, put, delete}. -/
structure AbstractSpec (S : Type) (Op : Type) where
  /-- The initial state predicate (what states are valid starting points) -/
  init : S → Prop
  /-- Specification for each operation -/
  opSpec : Op → OpSpec S
  /-- System invariant that must hold between all operations -/
  inv : S → Prop

/-! # Refinement -/

/-- A simulation relation between abstract state S and concrete state C.
    `rel c s` means "concrete state c represents abstract state s". -/
abbrev SimRel (S C : Type) := C → S → Prop

/-- A single operation refinement: the concrete L1 body refines an abstract
    operation specification via a simulation relation.

    Given:
    - Abstract operation spec (pre_abs, post_abs)
    - Concrete L1 body
    - Simulation relation R : C -> S -> Prop

    The refinement says: for any concrete state c and abstract state s
    related by R, if the abstract precondition holds on s, then:
    1. The concrete computation does not fail
    2. Every concrete result state c' is related to some abstract state s'
       that satisfies the abstract postcondition.

    This is backward simulation: concrete behaviors are contained in
    abstract behaviors. -/
def opRefinement {S C : Type}
    (absOp : OpSpec S) (concreteBody : L1Monad C)
    (R : SimRel S C) : Prop :=
  ∀ (c : C) (s : S),
    R c s → absOp.pre s →
    ¬(concreteBody c).failed ∧
    ∀ (rv : Except Unit Unit) (c' : C),
      (rv, c') ∈ (concreteBody c).results →
      -- On normal return, the result refines some abstract post-state
      (rv = Except.ok () → ∃ s', R c' s' ∧ absOp.post s s') ∧
      -- On error return, we still maintain the simulation relation
      (rv = Except.error () → ∃ s', R c' s')

/-- Simplified refinement for total (non-failing, non-throwing) operations.
    Most functions return normally, so this is the common case. -/
def opRefinementTotal {S C : Type}
    (absOp : OpSpec S) (concreteBody : L1Monad C)
    (R : SimRel S C) : Prop :=
  ∀ (c : C) (s : S),
    R c s → absOp.pre s →
    ¬(concreteBody c).failed ∧
    ∀ (rv : Except Unit Unit) (c' : C),
      (rv, c') ∈ (concreteBody c).results →
      ∃ s', R c' s' ∧ absOp.post s s'

/-- A full system refinement: every operation in the abstract spec
    is refined by a corresponding concrete L1 body. -/
structure SystemRefinement (S C : Type) (Op : Type) where
  /-- The abstract specification -/
  spec : AbstractSpec S Op
  /-- Map from operation index to concrete L1 body -/
  impl : Op → L1Monad C
  /-- The simulation relation -/
  rel : SimRel S C
  /-- Every operation refines its abstract spec -/
  refines : ∀ (op : Op), opRefinement (spec.opSpec op) (impl op) rel
  /-- The simulation relation preserves the abstract invariant -/
  inv_preserved : ∀ (op : Op) (c : C) (s : S),
    rel c s → spec.inv s → (spec.opSpec op).pre s →
    ∀ (rv : Except Unit Unit) (c' : C),
      (rv, c') ∈ ((impl op) c).results →
      ∀ s', rel c' s' → spec.inv s'

/-! # Composition: refinement implies abstract properties hold on concrete -/

/-- If a concrete body refines an abstract op, then any property proved
    about the abstract post-state also holds (up to simulation) on
    the concrete post-state.

    This is the main payoff: prove properties on the clean abstract spec,
    get them for free on the concrete C code. -/
theorem refinement_transfers_property {S C : Type}
    {absOp : OpSpec S} {body : L1Monad C} {R : SimRel S C}
    (h_ref : opRefinementTotal absOp body R)
    (P : S → Prop)
    (h_prop : ∀ s s', absOp.pre s → absOp.post s s' → P s') :
    ∀ (c : C) (s : S),
      R c s → absOp.pre s →
      ∀ rv c', (rv, c') ∈ (body c).results →
        ∃ s', R c' s' ∧ P s' := by
  intro c s h_rel h_pre rv c' h_mem
  have ⟨_, h_post⟩ := h_ref c s h_rel h_pre
  obtain ⟨s', h_rel', h_abs_post⟩ := h_post rv c' h_mem
  exact ⟨s', h_rel', h_prop s s' h_pre h_abs_post⟩

/-- Refinement composes with FuncSpec: if a body satisfies a FuncSpec
    and the FuncSpec implies the refinement conditions, then the
    refinement holds.

    This connects the per-function verification (FuncSpec) with the
    system-level specification (AbstractSpec). -/
theorem funcSpec_implies_refinement {S C : Type}
    {absOp : OpSpec S} {body : L1Monad C} {R : SimRel S C}
    {fspec : FuncSpec C}
    (h_sat : fspec.satisfiedBy body)
    (h_pre : ∀ c s, R c s → absOp.pre s → fspec.pre c)
    (h_post : ∀ c s rv c',
      R c s → absOp.pre s → fspec.post rv c' →
      (rv = Except.ok () → ∃ s', R c' s' ∧ absOp.post s s') ∧
      (rv = Except.error () → ∃ s', R c' s')) :
    opRefinement absOp body R := by
  intro c s h_rel h_abs_pre
  have h_fpre := h_pre c s h_rel h_abs_pre
  have ⟨h_nf, h_fpost⟩ := h_sat c h_fpre
  exact ⟨h_nf, fun rv c' h_mem => h_post c s rv c' h_rel h_abs_pre (h_fpost rv c' h_mem)⟩

/-! # Example: Abstract Key-Value Store

A simple key-value store with get/put operations.
The abstract state is a function from keys to optional values. -/

namespace KVStoreExample

/-- Keys are natural numbers (abstracting uint32_t indices). -/
abbrev Key := Nat

/-- Values are natural numbers. -/
abbrev Value := Nat

/-- Abstract state: a partial function from keys to values,
    with a fixed capacity. -/
structure KVState where
  store : Key → Option Value
  capacity : Nat

/-- Operations on the key-value store. -/
inductive KVOp where
  | get (k : Key)
  | put (k : Key) (v : Value)
  | size

/-- Abstract spec for the key-value store. -/
def kvSpec : AbstractSpec KVState KVOp where
  init := fun s => s.store = (fun _ => none) ∧ s.capacity > 0
  opSpec := fun op => match op with
    | .get _k => {
        pre := fun _ => True
        post := fun s s' => s'.store = s.store ∧ s'.capacity = s.capacity
      }
    | .put k v => {
        pre := fun _ => True
        post := fun s s' =>
          s'.store k = some v ∧
          (∀ k', k' ≠ k → s'.store k' = s.store k') ∧
          s'.capacity = s.capacity
      }
    | .size => {
        pre := fun _ => True
        post := fun s s' => s' = s  -- size is read-only
      }
  inv := fun s => s.capacity > 0

/-- The abstract spec satisfies: put then get returns the value. -/
theorem kv_put_get (s : KVState) (k : Key) (v : Value) (s' : KVState)
    (h_put : (kvSpec.opSpec (.put k v)).post s s') :
    s'.store k = some v := by
  exact h_put.1

/-- The abstract spec satisfies: put preserves other keys. -/
theorem kv_put_other (s : KVState) (k k' : Key) (v : Value) (s' : KVState)
    (h_put : (kvSpec.opSpec (.put k v)).post s s')
    (h_neq : k' ≠ k) :
    s'.store k' = s.store k' := by
  exact h_put.2.1 k' h_neq

/-- Get is read-only: state is unchanged. -/
theorem kv_get_readonly (s s' : KVState) (k : Key)
    (h_get : (kvSpec.opSpec (.get k)).post s s') :
    s'.store = s.store ∧ s'.capacity = s.capacity :=
  h_get

end KVStoreExample

/-! # Documentation: How to write specs for new systems

To specify and verify a new C module:

1. **Define the abstract state type**: a Lean structure capturing the
   essential state, free of C implementation details (no pointers,
   no byte arrays, no UInt32 overflow concerns).

2. **Define the operations**: an inductive type listing each function
   in the C module.

3. **Write the AbstractSpec**: for each operation, specify pre/post
   conditions over the abstract state. Include a system invariant.

4. **Define the simulation relation**: how does the concrete C state
   (ProgramState with heap, locals, etc.) map to the abstract state?
   This is where pointer dereferencing, UInt32.toNat conversion, etc.
   happen.

5. **Prove opRefinement for each function**: show that the concrete
   L1 body refines the abstract operation spec. Use funcSpec_implies_refinement
   to connect with existing FuncSpec proofs.

6. **Prove abstract properties**: properties about the abstract spec
   transfer to the concrete implementation via refinement_transfers_property.

Key principle: the abstract spec should be OBVIOUSLY correct. It should
be readable by someone who doesn't know C or Lean proofs. The proofs
connect this obvious spec to the actual C code.
-/
