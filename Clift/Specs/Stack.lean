-- Stack: Reusable abstract specification for a bounded LIFO stack
--
-- Abstract state: a List with capacity bound, top element at head.
-- Operations: push, pop, peek, size, isEmpty, isFull, clear.
-- Key properties: LIFO ordering, push/pop inverse, bounded size.
--
-- To instantiate: define simulation relation, prove opRefinement per operation.

import Clift.Lifting.AbstractSpec

namespace Specs.Stack

/-- Abstract state for a bounded LIFO stack of elements of type A. -/
structure StackState (A : Type) where
  /-- Stack contents, top element at head of list -/
  elems : List A
  /-- Maximum capacity -/
  capacity : Nat
  deriving Repr

/-- Operations on the stack. -/
inductive StackOp (A : Type) where
  | push (val : A)
  | pop
  | peek
  | size
  | isEmpty
  | isFull
  | clear

/-- Abstract specification for a bounded LIFO stack. -/
def stackSpec (A : Type) : AbstractSpec (StackState A) (StackOp A) where
  init := fun s => s.elems = [] ∧ s.capacity > 0
  opSpec := fun op => match op with
    | .push val => {
        pre := fun s => s.elems.length < s.capacity
        post := fun s s' => s'.elems = val :: s.elems ∧ s'.capacity = s.capacity
      }
    | .pop => {
        pre := fun s => s.elems ≠ []
        post := fun s s' =>
          ∃ top rest, s.elems = top :: rest ∧ s'.elems = rest ∧ s'.capacity = s.capacity
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

/-- LIFO: push then pop returns the pushed value and restores the stack. -/
theorem push_pop_inverse {A : Type} (s : StackState A) (v : A) (s_push s_pop : StackState A)
    (h_push : ((stackSpec A).opSpec (.push v)).post s s_push)
    (h_pop : ((stackSpec A).opSpec .pop).post s_push s_pop) :
    s_pop.elems = s.elems := by
  obtain ⟨h_push_elems, _⟩ := h_push
  obtain ⟨top, rest, h_split, h_pop_elems, _⟩ := h_pop
  rw [h_push_elems] at h_split
  have h_cons := List.cons.inj h_split
  rw [h_pop_elems, h_cons.2]

/-- Peek does not modify the stack. -/
theorem peek_readonly {A : Type} (s s' : StackState A)
    (h_peek : ((stackSpec A).opSpec .peek).post s s') :
    s' = s := h_peek

/-- Size after push is size + 1. -/
theorem size_after_push {A : Type} (s s' : StackState A) (v : A)
    (h_push : ((stackSpec A).opSpec (.push v)).post s s') :
    s'.elems.length = s.elems.length + 1 := by
  obtain ⟨h_elems, _⟩ := h_push
  rw [h_elems]; simp

/-- Invariant preserved by push. -/
theorem inv_push {A : Type} (s s' : StackState A) (v : A)
    (h_inv : (stackSpec A).inv s)
    (h_pre : ((stackSpec A).opSpec (.push v)).pre s)
    (h_post : ((stackSpec A).opSpec (.push v)).post s s') :
    (stackSpec A).inv s' := by
  simp only [stackSpec] at h_post h_inv h_pre ⊢
  obtain ⟨h_len, h_cap⟩ := h_inv
  obtain ⟨h_elems, h_cap'⟩ := h_post
  constructor
  · rw [h_elems]; simp; omega
  · omega

/-- Invariant preserved by pop. -/
theorem inv_pop {A : Type} (s s' : StackState A)
    (h_inv : (stackSpec A).inv s)
    (h_post : ((stackSpec A).opSpec .pop).post s s') :
    (stackSpec A).inv s' := by
  simp only [stackSpec] at h_post h_inv ⊢
  obtain ⟨h_len, h_cap⟩ := h_inv
  obtain ⟨_, rest, h_split, h_elems, h_cap'⟩ := h_post
  constructor
  · rw [h_elems, h_cap']
    have : s.elems.length = rest.length + 1 := by rw [h_split]; simp
    omega
  · omega

/-! # Instantiation Guide

To verify a concrete C stack (e.g., array-based):

```
-- 1. Import
import Generated.MyStack
import Clift.Specs.Stack

-- 2. Simulation relation: array + top index -> List
def myStackSim (cs : MyStack.ProgramState) (as : Specs.Stack.StackState Nat) : Prop :=
  -- as.elems = [array[top-1], array[top-2], ..., array[0]]
  -- as.capacity = STACK_SIZE

-- 3. Prove opRefinement for push, pop, etc.
-- 4. Properties transfer: push_pop_inverse guarantees correct LIFO behavior
```
-/

end Specs.Stack
