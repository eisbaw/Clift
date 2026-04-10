-- Queue: Reusable abstract specification for a bounded FIFO queue
--
-- Abstract state: a List with a capacity bound.
-- Operations: push, pop, peek, size, isEmpty, isFull, clear.
-- Key properties: FIFO ordering, bounded size, push/pop inverse.
--
-- To instantiate for your C data structure:
-- 1. Define a simulation relation mapping your concrete state to QueueState
-- 2. Prove opRefinement for each operation
-- 3. All abstract properties transfer automatically via refinement
--
-- Reference: Clift/Lifting/AbstractSpec.lean

import Clift.Lifting.AbstractSpec

namespace Specs.Queue

/-- Abstract state for a bounded FIFO queue of elements of type A. -/
structure QueueState (A : Type) where
  /-- Queue contents, front element at head of list -/
  elems : List A
  /-- Maximum capacity -/
  capacity : Nat
  deriving Repr

/-- Operations on the queue. -/
inductive QueueOp (A : Type) where
  | push (val : A)
  | pop
  | peek
  | size
  | isEmpty
  | isFull
  | clear

/-- Abstract specification for a bounded FIFO queue. -/
def queueSpec (A : Type) : AbstractSpec (QueueState A) (QueueOp A) where
  init := fun s => s.elems = [] ∧ s.capacity > 0
  opSpec := fun op => match op with
    | .push val => {
        pre := fun s => s.elems.length < s.capacity
        post := fun s s' => s'.elems = s.elems ++ [val] ∧ s'.capacity = s.capacity
      }
    | .pop => {
        pre := fun s => s.elems ≠ []
        post := fun s s' =>
          ∃ v rest, s.elems = v :: rest ∧ s'.elems = rest ∧ s'.capacity = s.capacity
      }
    | .peek => {
        pre := fun s => s.elems ≠ []
        post := fun s s' => s' = s
      }
    | .size => {
        pre := fun _ => True
        post := fun s s' => s' = s
      }
    | .isEmpty => {
        pre := fun _ => True
        post := fun s s' => s' = s
      }
    | .isFull => {
        pre := fun _ => True
        post := fun s s' => s' = s
      }
    | .clear => {
        pre := fun _ => True
        post := fun _ s' => s'.elems = [] ∧ s'.capacity > 0
      }
  inv := fun s => s.elems.length ≤ s.capacity ∧ s.capacity > 0

/-! # Key Properties -/

/-- FIFO: push then pop on a non-empty queue removes the front element. -/
theorem fifo {A : Type} (s : QueueState A) (v : A) (s_push s_pop : QueueState A)
    (h_push : ((queueSpec A).opSpec (.push v)).post s s_push)
    (h_pop : ((queueSpec A).opSpec .pop).post s_push s_pop)
    (h_nonempty : s.elems ≠ []) :
    ∃ front rest, s.elems = front :: rest ∧
      s_pop.elems = rest ++ [v] := by
  obtain ⟨h_push_elems, _⟩ := h_push
  obtain ⟨w, rest, h_split, h_pop_elems, _⟩ := h_pop
  rw [h_push_elems] at h_split
  obtain ⟨hd, tl, h_eq⟩ : ∃ hd tl, s.elems = hd :: tl := by
    cases h : s.elems with
    | nil => exact absurd h h_nonempty
    | cons hd tl => exact ⟨hd, tl, rfl⟩
  refine ⟨hd, tl, h_eq, ?_⟩
  rw [h_eq] at h_split
  have h_cons : hd :: (tl ++ [v]) = w :: rest := h_split
  have h_rest : rest = tl ++ [v] := (List.cons.inj h_cons).2.symm
  rw [h_pop_elems, h_rest]

/-- Push on empty then pop gives back the pushed value and empties the queue. -/
theorem push_pop_empty {A : Type} (s : QueueState A) (v : A) (s_push s_pop : QueueState A)
    (h_empty : s.elems = [])
    (h_push : ((queueSpec A).opSpec (.push v)).post s s_push)
    (h_pop : ((queueSpec A).opSpec .pop).post s_push s_pop) :
    s_pop.elems = [] := by
  obtain ⟨h_push_elems, _⟩ := h_push
  obtain ⟨w, rest, h_split, h_pop_elems, _⟩ := h_pop
  rw [h_push_elems, h_empty] at h_split
  have : [v] = w :: rest := h_split
  have h_rest := (List.cons.inj this).2
  rw [h_pop_elems, h_rest]

/-- Size after push is size + 1. -/
theorem size_after_push {A : Type} (s s' : QueueState A) (v : A)
    (h_push : ((queueSpec A).opSpec (.push v)).post s s') :
    s'.elems.length = s.elems.length + 1 := by
  obtain ⟨h_elems, _⟩ := h_push
  rw [h_elems, List.length_append, List.length_singleton]

/-- Invariant preserved by push. -/
theorem inv_push {A : Type} (s s' : QueueState A) (v : A)
    (h_inv : (queueSpec A).inv s)
    (h_pre : ((queueSpec A).opSpec (.push v)).pre s)
    (h_post : ((queueSpec A).opSpec (.push v)).post s s') :
    (queueSpec A).inv s' := by
  simp only [queueSpec] at h_post h_inv h_pre ⊢
  obtain ⟨h_len, h_cap⟩ := h_inv
  obtain ⟨h_elems, h_cap'⟩ := h_post
  constructor
  · rw [h_elems, List.length_append, List.length_singleton]; omega
  · omega

/-- Invariant preserved by pop. -/
theorem inv_pop {A : Type} (s s' : QueueState A)
    (h_inv : (queueSpec A).inv s)
    (h_post : ((queueSpec A).opSpec .pop).post s s') :
    (queueSpec A).inv s' := by
  simp only [queueSpec] at h_post h_inv ⊢
  obtain ⟨h_len, h_cap⟩ := h_inv
  obtain ⟨_, rest, h_split, h_elems, h_cap'⟩ := h_post
  constructor
  · rw [h_elems, h_cap']
    have : s.elems.length = rest.length + 1 := by rw [h_split]; simp
    omega
  · omega

/-- Clear preserves invariant. -/
theorem inv_clear {A : Type} (s s' : QueueState A)
    (_h_inv : (queueSpec A).inv s)
    (h_post : ((queueSpec A).opSpec .clear).post s s') :
    (queueSpec A).inv s' := by
  obtain ⟨h_elems, h_cap⟩ := h_post
  exact ⟨by rw [h_elems]; simp, h_cap⟩

/-! # Instantiation Guide

To verify a concrete C queue implementation:

```
-- 1. Import the generated C code and the queue spec
import Generated.MyQueue
import Clift.Specs.Queue

-- 2. Define the simulation relation
def myQueueSim (cs : MyQueue.ProgramState) (as : Specs.Queue.QueueState Nat) : Prop :=
  -- Map C struct fields to abstract state
  -- Map linked list to Lean List
  -- Map uint32_t count to Nat length

-- 3. For each operation, prove refinement:
theorem push_refines :
    opRefinement ((Specs.Queue.queueSpec Nat).opSpec (.push v))
      MyQueue.l1_push_body myQueueSim := by
  ...

-- 4. Abstract properties (fifo, size_after_push, etc.) transfer automatically
```
-/

end Specs.Queue
