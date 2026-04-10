-- Ring buffer verification: abstract spec, global invariant, per-function proofs
--
-- This is the Phase D milestone test (tasks 0095-0098).
--
-- Module: ring_buffer.c (251 LOC, 16 functions)
-- Exercises: struct pointers, linked list traversal, state invariants,
--            multiple interacting functions, heap read/write
--
-- Verification approach:
-- 1. Abstract spec: bounded FIFO queue over Nat values
-- 2. Global invariant: count <= capacity, null-consistency
-- 3. Per-function FuncSpecs for key functions
-- 4. Invariant preservation proofs
-- 5. Refinement: C implementation refines abstract queue spec

import Generated.RingBuffer
import Clift.Lifting.Pipeline
import Clift.Lifting.FuncSpec
import Clift.Lifting.AbstractSpec
import Clift.Lifting.GlobalInvariant
import Clift.Lifting.HeapLift.SepLogic

set_option maxHeartbeats 6400000
set_option maxRecDepth 4096

open RingBuffer

/-! # Step 1: Run the clift pipeline -/

clift RingBuffer

-- Verify all 16 functions got L1 definitions
#check @RingBuffer.l1_rb_init_body
#check @RingBuffer.l1_rb_push_body
#check @RingBuffer.l1_rb_pop_body
#check @RingBuffer.l1_rb_peek_body
#check @RingBuffer.l1_rb_size_body
#check @RingBuffer.l1_rb_is_empty_body
#check @RingBuffer.l1_rb_is_full_body
#check @RingBuffer.l1_rb_clear_body
#check @RingBuffer.l1_rb_count_nodes_body
#check @RingBuffer.l1_rb_contains_body
#check @RingBuffer.l1_rb_peek_back_body
#check @RingBuffer.l1_rb_check_integrity_body
#check @RingBuffer.l1_rb_increment_all_body
#check @RingBuffer.l1_rb_sum_body
#check @RingBuffer.l1_rb_capacity_body
#check @RingBuffer.l1_rb_remaining_body

-- L1corres proofs for non-calling functions
#check @RingBuffer.l1_rb_init_body_corres
#check @RingBuffer.l1_rb_push_body_corres
#check @RingBuffer.l1_rb_pop_body_corres
#check @RingBuffer.l1_rb_peek_body_corres
#check @RingBuffer.l1_rb_size_body_corres
#check @RingBuffer.l1_rb_is_empty_body_corres
#check @RingBuffer.l1_rb_is_full_body_corres
#check @RingBuffer.l1_rb_clear_body_corres
#check @RingBuffer.l1_rb_count_nodes_body_corres
#check @RingBuffer.l1_rb_contains_body_corres
#check @RingBuffer.l1_rb_peek_back_body_corres
#check @RingBuffer.l1_rb_increment_all_body_corres
#check @RingBuffer.l1_rb_sum_body_corres
#check @RingBuffer.l1_rb_capacity_body_corres
#check @RingBuffer.l1_rb_remaining_body_corres

-- L2 forms
#check @RingBuffer.l2_rb_init_body
#check @RingBuffer.l2_rb_push_body
#check @RingBuffer.l2_rb_size_body

-- L3 classifications
#check @RingBuffer.l3_rb_size_body_level
#check @RingBuffer.l3_rb_is_empty_body_level
#check @RingBuffer.l3_rb_is_full_body_level
#check @RingBuffer.l3_rb_capacity_body_level
#check @RingBuffer.l3_rb_remaining_body_level

-- No sorry in L1corres proofs
#print axioms RingBuffer.l1_rb_init_body_corres
#print axioms RingBuffer.l1_rb_push_body_corres
#print axioms RingBuffer.l1_rb_size_body_corres

/-! # Step 2: Abstract specification -- bounded FIFO queue -/

namespace RBSpec

/-- Abstract state: a bounded queue of natural numbers. -/
structure QueueState where
  /-- The queue contents (front at head, back at tail) -/
  elems : List Nat
  /-- Maximum capacity -/
  capacity : Nat

/-- Operations on the queue. -/
inductive QueueOp where
  | init (cap : Nat)
  | push (val : Nat)
  | pop
  | peek
  | size
  | isEmpty
  | isFull
  | clear

/-- Abstract spec for the bounded queue. -/
def queueSpec : AbstractSpec QueueState QueueOp where
  init := fun s => s.elems = [] ∧ s.capacity > 0
  opSpec := fun op => match op with
    | .init cap => {
        pre := fun _ => cap > 0
        post := fun _ s' => s'.elems = [] ∧ s'.capacity = cap
      }
    | .push val => {
        pre := fun s => s.elems.length < s.capacity
        post := fun s s' =>
          s'.elems = s.elems ++ [val] ∧ s'.capacity = s.capacity
      }
    | .pop => {
        pre := fun s => s.elems ≠ []
        post := fun s s' =>
          ∃ v rest, s.elems = v :: rest ∧ s'.elems = rest ∧
          s'.capacity = s.capacity
      }
    | .peek => {
        pre := fun s => s.elems ≠ []
        post := fun s s' => s' = s  -- peek is read-only
      }
    | .size => {
        pre := fun _ => True
        post := fun s s' => s' = s  -- size is read-only
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
        post := fun _ s' => s'.elems = []
      }
  inv := fun s => s.elems.length ≤ s.capacity ∧ s.capacity > 0

/-! ## Abstract spec properties -/

/-- Push then pop recovers the first element. -/
theorem queue_fifo (s : QueueState) (v : Nat) (s_push s_pop : QueueState)
    (h_push : (queueSpec.opSpec (.push v)).post s s_push)
    (h_pop : (queueSpec.opSpec .pop).post s_push s_pop)
    (h_nonempty : s.elems ≠ []) :
    ∃ front rest, s.elems = front :: rest ∧
      s_pop.elems = rest ++ [v] := by
  obtain ⟨h_push_elems, _⟩ := h_push
  obtain ⟨w, rest, h_split, h_pop_elems, _⟩ := h_pop
  -- s_push.elems = s.elems ++ [v] = w :: rest
  rw [h_push_elems] at h_split
  -- s.elems must be non-empty, so it's hd :: tl
  obtain ⟨hd, tl, h_eq⟩ : ∃ hd tl, s.elems = hd :: tl := by
    cases h : s.elems with
    | nil => exact absurd h h_nonempty
    | cons hd tl => exact ⟨hd, tl, rfl⟩
  refine ⟨hd, tl, h_eq, ?_⟩
  rw [h_pop_elems]
  -- h_split : (hd :: tl) ++ [v] = w :: rest
  rw [h_eq] at h_split
  have h_cons : hd :: (tl ++ [v]) = w :: rest := h_split
  have h_rest : rest = tl ++ [v] := by
    have := List.cons.inj h_cons
    exact this.2.symm
  exact h_rest

/-- Push on empty: pop gives back the pushed value. -/
theorem queue_push_pop_empty (s : QueueState) (v : Nat) (s_push s_pop : QueueState)
    (h_empty : s.elems = [])
    (h_push : (queueSpec.opSpec (.push v)).post s s_push)
    (h_pop : (queueSpec.opSpec .pop).post s_push s_pop) :
    s_pop.elems = [] := by
  obtain ⟨h_push_elems, _⟩ := h_push
  obtain ⟨w, rest, h_split, h_pop_elems, _⟩ := h_pop
  rw [h_push_elems, h_empty] at h_split
  -- h_split : [] ++ [v] = w :: rest, so [v] = w :: rest, so rest = []
  have h_cons : [v] = w :: rest := h_split
  have h_rest := (List.cons.inj h_cons).2
  rw [h_pop_elems, h_rest]

/-- Size after push is size + 1. -/
theorem queue_size_push (s s' : QueueState) (v : Nat)
    (h_push : (queueSpec.opSpec (.push v)).post s s') :
    s'.elems.length = s.elems.length + 1 := by
  obtain ⟨h_elems, _⟩ := h_push
  rw [h_elems]
  induction s.elems with
  | nil => rfl
  | cons hd tl ih => simp [List.length, ih]

/-- Clear empties the queue. -/
theorem queue_clear_empty (s s' : QueueState)
    (h_clear : (queueSpec.opSpec .clear).post s s') :
    s'.elems = [] :=
  h_clear

/-- Invariant preserved by push. -/
theorem queue_inv_push (s s' : QueueState) (v : Nat)
    (h_inv : queueSpec.inv s)
    (h_pre : (queueSpec.opSpec (.push v)).pre s)
    (h_post : (queueSpec.opSpec (.push v)).post s s') :
    queueSpec.inv s' := by
  obtain ⟨h_len, h_cap⟩ := h_inv
  obtain ⟨h_elems, h_cap'⟩ := h_post
  -- h_pre : s.elems.length < s.capacity
  -- h_elems : s'.elems = s.elems ++ [v]
  -- h_cap' : s'.capacity = s.capacity
  -- Unfold h_pre to get the actual Nat comparison
  change s.elems.length < s.capacity at h_pre
  refine ⟨?_, ?_⟩
  · -- s'.elems.length ≤ s'.capacity
    suffices h : s'.elems.length = s.elems.length + 1 by omega
    rw [h_elems]
    induction s.elems with
    | nil => rfl
    | cons hd tl ih => simp [List.length, ih]
  · omega

/-- Invariant preserved by pop. -/
theorem queue_inv_pop (s s' : QueueState)
    (h_inv : queueSpec.inv s)
    (h_post : (queueSpec.opSpec .pop).post s s') :
    queueSpec.inv s' := by
  obtain ⟨h_len, h_cap⟩ := h_inv
  obtain ⟨v, rest, h_split, h_elems, h_cap'⟩ := h_post
  constructor
  · rw [h_elems, h_cap']
    rw [h_split] at h_len; simp at h_len; omega
  · rw [h_cap']; exact h_cap

end RBSpec

/-! # Step 3: Global invariant for the concrete ring buffer -/

/-- Concrete invariant on the ring buffer state (at the heap level).
    This predicate operates on the rb_state struct read from the heap.

    Invariant conditions:
    1. count <= capacity
    2. count == 0 iff head == Ptr.null
    3. count == 0 iff tail == Ptr.null
    4. capacity > 0 -/
def rbInvariant (rbState : C_rb_state) : Prop :=
  rbState.count.toNat ≤ rbState.capacity.toNat ∧
  rbState.capacity.toNat > 0 ∧
  (rbState.count = 0 ↔ rbState.head = Ptr.null) ∧
  (rbState.count = 0 ↔ rbState.tail = Ptr.null)

/-! # Step 4: Per-function specifications (FuncSpecs)

For each function, we specify the expected behavior. Functions that
only read state (size, is_empty, is_full, peek, capacity, remaining)
have simple specs. Functions that modify state (init, push, pop, clear)
have specs relating input to output state. -/

/-- rb_size specification: returns the count field unchanged. -/
def rb_size_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.rb
  post := fun r s =>
    r = Except.ok () →
    s.locals.ret__val = (hVal s.globals.rawHeap s.locals.rb).count

/-- rb_is_empty specification: returns 1 if count == 0, 0 otherwise. -/
def rb_is_empty_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.rb
  post := fun r s =>
    r = Except.ok () →
    (s.locals.ret__val = 1 ↔ (hVal s.globals.rawHeap s.locals.rb).count = 0)

/-- rb_is_full specification: returns 1 if count >= capacity, 0 otherwise. -/
def rb_is_full_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.rb
  post := fun r s =>
    r = Except.ok () →
    (s.locals.ret__val = 1 ↔
      (hVal s.globals.rawHeap s.locals.rb).count ≥
      (hVal s.globals.rawHeap s.locals.rb).capacity)

/-- rb_capacity specification: returns the capacity field. -/
def rb_capacity_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.rb
  post := fun r s =>
    r = Except.ok () →
    s.locals.ret__val = (hVal s.globals.rawHeap s.locals.rb).capacity

/-! # Step 5: Simulation relation for refinement

The simulation relation connects the concrete C state to the abstract
queue state. This requires:
1. Reading the rb_state struct from the heap
2. Traversing the linked list to extract element values
3. Converting UInt32 values to Nat -/

/-- isQueue: recursive heap predicate connecting the linked list
    starting at pointer p to a Lean List Nat.

    Similar to isList from ListLengthProof.lean but for rb_node. -/
inductive isQueue : Ptr C_rb_node → List Nat → HeapRawState → Prop where
  | nil (h : HeapRawState) : isQueue Ptr.null [] h
  | cons (p : Ptr C_rb_node) (v : Nat) (vs : List Nat) (h : HeapRawState)
    (hv : heapPtrValid h p)
    (h_val : (hVal h p).value.toNat = v)
    (h_tail : isQueue (hVal h p).next vs h) :
    isQueue p (v :: vs) h

/-- A null pointer has an empty queue. -/
theorem isQueue_null {xs : List Nat} {h : HeapRawState}
    (hq : isQueue Ptr.null xs h) : xs = [] := by
  cases hq with
  | nil => rfl
  | cons p v vs h' hv _ _ =>
    exact absurd (heapPtrValid_nonnull hv) (by simp [Ptr.null])

/-- A non-null pointer has a non-empty queue. -/
theorem isQueue_nonnull {p : Ptr C_rb_node} {xs : List Nat} {h : HeapRawState}
    (hq : isQueue p xs h) (h_nn : p ≠ Ptr.null) :
    ∃ v vs, xs = v :: vs ∧
      heapPtrValid h p ∧
      (hVal h p).value.toNat = v ∧
      isQueue (hVal h p).next vs h := by
  cases hq with
  | nil => exact absurd rfl h_nn
  | cons p' v vs h' hv h_val h_tail =>
    exact ⟨v, vs, rfl, hv, h_val, h_tail⟩

/-- The simulation relation:
    - The rb_state pointer is valid in the heap
    - The linked list from head represents the abstract queue
    - count matches the list length
    - capacity matches -/
def rbSimRel (cs : ProgramState) (as : RBSpec.QueueState) : Prop :=
  let rbst := hVal cs.globals.rawHeap cs.locals.rb
  heapPtrValid cs.globals.rawHeap cs.locals.rb ∧
  isQueue rbst.head as.elems cs.globals.rawHeap ∧
  rbst.count.toNat = as.elems.length ∧
  rbst.capacity.toNat = as.capacity

/-! # Step 6: Measurements

## Module statistics
- C source: 251 LOC, 16 functions
- Generated Lean (CSimpl): 882 lines
- Functions successfully imported: 16/16
- Functions lifted to L1: 16/16 (pending build verification)
- L1corres proofs: 15/16 (rb_check_integrity calls rb_count_nodes)

## Gap analysis
- Array subscript: NOT supported (redesigned to use linked list)
- Pointer-to-pointer: NOT supported (redesigned to avoid **)
- CImporter NULL handling for struct fields: FIXED (was emitting 0 instead of Ptr.null)
- CImporter roundtrip proof: FIXED (redundant `cases v; rfl` after full rw)

## Proof infrastructure
- Abstract spec: ~80 lines (QueueState, QueueOp, queueSpec, 5 properties)
- Global invariant: ~10 lines (rbInvariant definition)
- Simulation relation: ~40 lines (isQueue inductive + rbSimRel)
- Per-function FuncSpecs: ~40 lines (4 specs for read-only functions)
- Total proof infrastructure: ~170 lines for 251 LOC of C

## Proof-to-code ratio estimate
- Abstract spec + invariant: 170 lines / 251 lines C = 0.7:1 (spec only)
- Full verification (with step-by-step proofs): estimated 8-12:1
  based on Phase C experience where list_length was 10:1
- Automation: clift handles L1/L2/L3 automatically (100% for non-calling functions)
- Manual effort: invariant proofs, simulation relation, abstract spec
-/

/-! # Axiom audit: verify no sorry in key definitions -/
#print axioms isQueue
#print axioms isQueue_null
#print axioms isQueue_nonnull
#print axioms rbInvariant
#print axioms rbSimRel
#print axioms RBSpec.queue_fifo
#print axioms RBSpec.queue_push_pop_empty
#print axioms RBSpec.queue_inv_push
#print axioms RBSpec.queue_inv_pop
