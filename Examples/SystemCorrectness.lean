-- Task 0138: Composed system-level correctness theorem
--
-- Defines SystemExec (sequence of operations) and proves that any sequence
-- on the C implementation produces results matching the abstract spec.
-- This composes per-function refinements into a single end-to-end guarantee.
--
-- Even with sorry in individual validHoare proofs, the THEOREM STATEMENT
-- is the main deliverable: it precisely defines what "system-level correctness" means.
--
-- Reference: seL4's system-level refinement (AInvs -> Refine -> CRefine chain)

import Examples.RBExtRefinement
import Clift.Lifting.AbstractSpec

set_option maxHeartbeats 12800000
set_option maxRecDepth 4096
set_option linter.unusedVariables false

open RBExtInvariant RBExtRefinement RingBufferExt

namespace SystemCorrectness

/-! # SystemExec: a sequence of operations on a system

    A SystemExec is a finite trace of operations. We model it as a list
    of abstract operations, paired with a function that executes each
    operation on the concrete state.

    The key theorem: if every individual operation refines the abstract spec,
    then ANY sequence of operations on the concrete system produces results
    consistent with the abstract spec. -/

/-- A system execution trace: a sequence of operations. -/
abbrev SystemExec (Op : Type) := List Op

/-! # Trace-based formulation

    Instead of indexed access (which causes omega issues with existential lengths),
    we define traces as recursive propositions over lists. -/

/-- A concrete trace: sequence of (operation, resulting-state) pairs. -/
abbrev ConcreteTrace (C Op : Type) := List (Op × C)

/-- A concrete trace is valid if each step executes successfully. -/
def validConcreteTrace {C Op : Type}
    (impl : Op → L1Monad C)
    (c₀ : C) : ConcreteTrace C Op → Prop
  | [] => True
  | (op, c') :: rest =>
    -- The operation does not fail from the previous state
    ¬(impl op c₀).failed ∧
    -- The result state is reachable
    (Except.ok (), c') ∈ (impl op c₀).results ∧
    -- The rest of the trace continues from c'
    validConcreteTrace impl c' rest

/-- An abstract trace simulates a concrete trace if:
    1. Each abstract state is related to the corresponding concrete state
    2. Each abstract state satisfies the invariant
    3. Each abstract transition satisfies the postcondition -/
def abstractTraceSimulates {S C Op : Type}
    (spec : AbstractSpec S Op)
    (R : SimRel S C)
    (s₀ : S) (c₀ : C) : ConcreteTrace C Op → List S → Prop
  | [], [] => True
  | (op, c') :: crest, s' :: srest =>
    -- Abstract state related to concrete state
    R c' s' ∧
    -- Abstract invariant holds
    spec.inv s' ∧
    -- Abstract postcondition holds
    (spec.opSpec op).post s₀ s' ∧
    -- Rest of trace simulates from new states
    abstractTraceSimulates spec R s' c' crest srest
  | _, _ => False  -- Length mismatch

/-! # The system-level correctness theorem

    This is the main theorem: if we have a SystemRefinement (every operation
    individually refines its abstract spec), then any valid concrete trace
    can be simulated by an abstract trace. -/

/-- System-level correctness: valid concrete traces have simulating abstract traces.

    Given:
    - A SystemRefinement (individual operation refinements)
    - A valid concrete trace
    - Initial states related by the simulation relation
    - Abstract invariant and preconditions hold

    Then: there exists an abstract trace that simulates the concrete trace. -/
theorem system_exec_refines
    {S C Op : Type}
    (sr : SystemRefinement S C Op)
    (trace : ConcreteTrace C Op)
    (c₀ : C) (s₀ : S)
    (h_rel₀ : sr.rel c₀ s₀)
    (h_inv₀ : sr.spec.inv s₀)
    (h_valid : validConcreteTrace sr.impl c₀ trace)
    -- Abstract preconditions hold at each step (derived from invariant in practice)
    (h_pre : ∀ (op : Op) (c : C) (s : S),
      sr.rel c s → sr.spec.inv s → (sr.spec.opSpec op).pre s)
    :
    ∃ (atrace : List S),
      atrace.length = trace.length ∧
      abstractTraceSimulates sr.spec sr.rel s₀ c₀ trace atrace := by
  induction trace generalizing c₀ s₀ with
  | nil =>
    exact ⟨[], rfl, trivial⟩
  | cons step rest ih =>
    obtain ⟨op, c'⟩ := step
    obtain ⟨h_nf, h_mem, h_rest_valid⟩ := h_valid
    -- Use per-operation refinement to find abstract post-state
    have h_abs_pre := h_pre op c₀ s₀ h_rel₀ h_inv₀
    have ⟨_, h_ref⟩ := sr.refines op c₀ s₀ h_rel₀ h_abs_pre
    have h_ok := (h_ref (Except.ok ()) c' h_mem).1 rfl
    obtain ⟨s', h_rel', h_post'⟩ := h_ok
    -- Need invariant preservation for the recursive call
    have h_inv' : sr.spec.inv s' := by
      have := sr.inv_preserved op c₀ s₀ h_rel₀ h_inv₀ h_abs_pre
        (Except.ok ()) c' h_mem s' h_rel'
      exact this
    -- Recurse for the rest of the trace
    have ⟨atrace_rest, h_len_rest, h_sim_rest⟩ :=
      ih c' s' h_rel' h_inv' h_rest_valid
    -- Build the full abstract trace
    exact ⟨s' :: atrace_rest,
           by simp [h_len_rest],
           ⟨h_rel', h_inv', h_post', h_sim_rest⟩⟩

/-! # Instantiation for ring_buffer_ext

    Apply the system-level theorem to the ring_buffer_ext implementation. -/

/-- System-level correctness for ring_buffer_ext: any valid concrete trace
    of ring buffer operations has a simulating abstract trace.

    This is the composition of ALL per-function refinements into ONE theorem:
      C source -> CSimpl -> L1 (via L1corres) -> FuncSpec -> opRefinement -> AbstractSpec

    Blocked on: rbExtSystemRefinement (which is blocked on task 0136 validHoare proofs). -/
theorem rb_ext_system_correct
    (trace : ConcreteTrace ProgramState ExtQueueOp)
    (c₀ : ProgramState) (s₀ : RBExtSpec.QueueState)
    (h_rel₀ : rbExtSimRel c₀ s₀)
    (h_inv₀ : queueInvariant s₀)
    (h_valid : validConcreteTrace extQueueImpl c₀ trace)
    (h_pre : ∀ (op : ExtQueueOp) (c : ProgramState) (s : RBExtSpec.QueueState),
      rbExtSimRel c s → queueInvariant s →
      (extQueueSpec.opSpec op).pre s)
    :
    ∃ (atrace : List RBExtSpec.QueueState),
      atrace.length = trace.length ∧
      abstractTraceSimulates extQueueSpec rbExtSimRel s₀ c₀ trace atrace :=
  system_exec_refines rbExtSystemRefinement trace c₀ s₀ h_rel₀ h_inv₀
    h_valid h_pre

/-! # Example: 10-operation sequence on ring buffer

    Acceptance criterion #4: demonstrate with a concrete 10-operation sequence. -/

/-- A 10-operation sequence: init, push x3, size, pop, peek, push, pop, pop -/
def example_10ops : SystemExec ExtQueueOp :=
  [ .init 10,
    .push 42,
    .push 17,
    .push 99,
    .size,
    .pop,
    .peek,
    .push 7,
    .pop,
    .pop ]

/-- abstractExec: there exist intermediate abstract states satisfying all pre/post. -/
def abstractExec {S : Type} {Op : Type}
    (spec : AbstractSpec S Op)
    (ops : SystemExec Op)
    (s₀ : S) : Prop :=
  match ops with
  | [] => True
  | [op] => (spec.opSpec op).pre s₀ ∧
             ∃ s', (spec.opSpec op).post s₀ s'
  | op :: rest =>
    (spec.opSpec op).pre s₀ ∧
    ∃ s', (spec.opSpec op).post s₀ s' ∧ abstractExec spec rest s'

/-- The 10-operation sequence is well-formed at the abstract level:
    starting from an initial state, all preconditions hold and all
    postconditions produce valid states. -/
theorem example_10ops_abstract_valid :
    ∀ (s₀ : RBExtSpec.QueueState),
      extQueueSpec.init s₀ →
      queueInvariant s₀ →
      abstractExec extQueueSpec example_10ops s₀
    := by
  intro s₀ ⟨h_elems, h_cap, h_pushes, h_pops⟩ _h_inv
  -- Unfold abstractExec for the 10-op trace and construct witnesses
  unfold example_10ops abstractExec
  simp only [extQueueSpec]
  -- op 1: init 10
  -- pre: 10 > 0
  refine ⟨by omega, ?_⟩
  -- post: s'.elems = [] ∧ s'.capacity = 10 ∧ s'.totalPushes = 0 ∧ s'.totalPops = 0
  refine ⟨⟨[], 10, 0, 0⟩, ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  -- op 2: push 42
  -- pre: [].length < 10
  refine ⟨by simp, ?_⟩
  refine ⟨⟨[42], 10, 1, 0⟩, ⟨by simp, rfl, rfl, rfl⟩, ?_⟩
  -- op 3: push 17
  refine ⟨by simp, ?_⟩
  refine ⟨⟨[42, 17], 10, 2, 0⟩, ⟨by simp, rfl, rfl, rfl⟩, ?_⟩
  -- op 4: push 99
  refine ⟨by simp, ?_⟩
  refine ⟨⟨[42, 17, 99], 10, 3, 0⟩, ⟨by simp, rfl, rfl, rfl⟩, ?_⟩
  -- op 5: size (read-only, state unchanged)
  refine ⟨trivial, ?_⟩
  refine ⟨⟨[42, 17, 99], 10, 3, 0⟩, rfl, ?_⟩
  -- op 6: pop
  -- pre: [42, 17, 99] ≠ []
  refine ⟨by simp, ?_⟩
  -- post: ∃ v rest, [42,17,99] = v :: rest ∧ s'.elems = rest ∧ ...
  refine ⟨⟨[17, 99], 10, 3, 1⟩, ⟨42, [17, 99], rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  -- op 7: peek (read-only)
  refine ⟨trivial, ?_⟩
  refine ⟨⟨[17, 99], 10, 3, 1⟩, rfl, ?_⟩
  -- op 8: push 7
  refine ⟨by simp, ?_⟩
  refine ⟨⟨[17, 99, 7], 10, 4, 1⟩, ⟨by simp, rfl, rfl, rfl⟩, ?_⟩
  -- op 9: pop
  refine ⟨by simp, ?_⟩
  refine ⟨⟨[99, 7], 10, 4, 2⟩, ⟨17, [99, 7], rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  -- op 10: pop (last element, uses single-op case)
  refine ⟨by simp, ?_⟩
  exact ⟨⟨[7], 10, 4, 3⟩, ⟨99, [7], rfl, rfl, rfl, rfl, rfl⟩⟩

/-! # Status and measurements

## Task 0138 deliverables:
1. SystemExec type: defined (List Op)
2. system_exec_refines theorem: PROVEN (no sorry!)
   - The theorem: any valid concrete trace has a simulating abstract trace
   - Uses per-operation refinement from SystemRefinement
   - Uses invariant preservation across operations
3. rb_ext_system_correct: instantiation for ring buffer (delegates to system_exec_refines)
4. Example: 10-operation sequence defined, abstract validity stated
   - 1 sorry (mechanical abstract trace construction)
5. ConcreteTrace / abstractTraceSimulates: clean recursive definitions

## Key achievement:
system_exec_refines is SORRY-FREE (modulo the sorry in rbExtSystemRefinement.inv_preserved
and .refines, which flow through). The theorem STATEMENT and PROOF STRUCTURE are complete.
The remaining sorry are in the INPUT data (the SystemRefinement instance), not in the
composition logic.

## sorry summary:
- system_exec_refines: 0 sorry in the proof itself
  (but uses sr.inv_preserved which has sorry in the rbExt instantiation)
- rb_ext_system_correct: 0 additional sorry (delegates)
- example_10ops_abstract_valid: PROVEN (sorry eliminated)
- Blocked on: task 0136 (validHoare proofs) for the rbExt sorry chain
-/

end SystemCorrectness
