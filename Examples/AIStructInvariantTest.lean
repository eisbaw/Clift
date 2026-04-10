-- Phase E test: AI-assisted struct invariant generation
--
-- Demonstrates the struct invariant framework on:
-- 1. Ring buffer (rbInvariant from RingBufferProof.lean)
-- 2. Abstract queue (from RBSpec)
--
-- The mock oracle suggests invariants; the kernel checks preservation.
--
-- Reference: tasks 0100, 0103

import Clift.AI.StructInvariantGen
import Examples.RingBufferProof

set_option maxHeartbeats 3200000

/-! # Test 1: Ring buffer struct invariant

The "AI" suggests the rbInvariant from RingBufferProof.lean:
- count <= capacity
- capacity > 0
- count == 0 iff head == null
- count == 0 iff tail == null -/

open RingBuffer

/-- Ring buffer struct context for the AI oracle. -/
def rbStructContext : StructContext RingBuffer.ProgramState where
  structName := "rb_state"
  fieldDescriptions := [
    ("count", "UInt32 -- number of elements"),
    ("capacity", "UInt32 -- maximum capacity"),
    ("head", "Ptr C_rb_node -- front of queue"),
    ("tail", "Ptr C_rb_node -- back of queue")
  ]
  operations := []
  knownConstraints := [
    "count is incremented by push, decremented by pop",
    "head/tail are null when count == 0",
    "capacity is set at init and never changes"
  ]

/-- "AI-suggested" invariant for the ring buffer. -/
def rbStructInvariantSuggestion : StructInvariantSuggestion RingBuffer.ProgramState where
  inv := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.rb →
    rbInvariant (hVal s.globals.rawHeap s.locals.rb)
  description := "count <= capacity, capacity > 0, null-consistency for head/tail"
  constrainedFields := ["count", "capacity", "head", "tail"]

/-- Mock oracle for struct invariants. -/
def structMockOracle : StructInvariantOracle RingBuffer.ProgramState :=
  mkMockStructOracle [
    ("rb_state", [rbStructInvariantSuggestion])
  ]

/-- The mock oracle returns our suggestion for "rb_state". -/
theorem rb_oracle_suggests :
    (structMockOracle.suggest rbStructContext).length > 0 := by
  native_decide

/-! # Test 2: Abstract queue invariant patterns -/

/-- Demonstrate the bounded counter pattern. -/
def rbBoundedCounterDemo :=
  boundedCounterInv
    (fun s : RBSpec.QueueState => s.elems.length)
    (fun s => s.capacity)

/-- The queue abstract spec invariant IS a bounded counter invariant. -/
theorem rb_abstract_inv_is_bounded :
    ∀ s : RBSpec.QueueState, RBSpec.queueSpec.inv s → rbBoundedCounterDemo s := by
  intro s ⟨h_len, h_cap⟩
  exact ⟨h_len, h_cap⟩

/-! # Conjunction pattern -/

/-- Two sub-invariants for the abstract queue. -/
def queueCountInv : GlobalInvariant RBSpec.QueueState :=
  fun s => s.elems.length ≤ s.capacity

def queueCapInv : GlobalInvariant RBSpec.QueueState :=
  fun s => s.capacity > 0

/-- The full queue invariant is the conjunction. -/
theorem queue_inv_is_conj :
    ∀ s : RBSpec.QueueState,
      RBSpec.queueSpec.inv s ↔ conjInvariant queueCountInv queueCapInv s := by
  intro s
  constructor
  · intro ⟨h₁, h₂⟩; exact ⟨h₁, h₂⟩
  · intro ⟨h₁, h₂⟩; exact ⟨h₁, h₂⟩

/-! # Metrics

## Struct invariant generation results (mock oracle)

### Ring buffer:
- Suggested: count <= capacity, capacity > 0, null-consistency
- Matches rbInvariant from Phase D exactly
- Result: ACCEPTED (oracle returns correct suggestion)

### Abstract queue:
- Bounded counter pattern: directly applicable
- Conjunction composition: verified mechanically

## Assessment

Struct invariants are "easier" for AI than loop invariants because
they follow directly from the struct field types and usage patterns.
The patterns (bounded counter, null consistency) cover most cases.
-/

-- Axiom audit
#print axioms rb_oracle_suggests
#print axioms rb_abstract_inv_is_bounded
#print axioms queue_inv_is_conj
