-- Task 0161: Priority queue (binary heap) verification
--
-- Array-based min-heap with pointer-based data array.
-- 10 functions imported from priority_queue.c (~120 LOC C -> ~459 lines Lean).
--
-- Key verification targets:
-- - Heap property: parent <= children
-- - extract_min returns minimum
-- - Size tracking correct
-- - Array bounds: all accesses within [0, size) (task 0186)

import Generated.PriorityQueue
import Clift.Lifting.Pipeline
import Clift.Lifting.FuncSpec

set_option maxHeartbeats 12800000
set_option maxRecDepth 4096

open PriorityQueue

/-! # Step 1: Run the clift pipeline on all 10 functions -/

clift PriorityQueue

/-! # Step 2: Verify L1 definitions exist -/

#check @PriorityQueue.l1_pq_init_body
#check @PriorityQueue.l1_pq_swap_body
#check @PriorityQueue.l1_pq_bubble_up_body
#check @PriorityQueue.l1_pq_bubble_down_body
#check @PriorityQueue.l1_pq_insert_body
#check @PriorityQueue.l1_pq_extract_min_body
#check @PriorityQueue.l1_pq_peek_body
#check @PriorityQueue.l1_pq_size_body
#check @PriorityQueue.l1_pq_is_empty_body
#check @PriorityQueue.l1_pq_is_full_body

/-! # Step 3: Abstract heap property -/

/-- Heap property for array-based min-heap:
    For every node i, data[i] <= data[2i+1] and data[i] <= data[2i+2]
    (when children exist). -/
def isMinHeap (data : Nat → Nat) (size : Nat) : Prop :=
  ∀ i, i < size →
    (2 * i + 1 < size → data i ≤ data (2 * i + 1)) ∧
    (2 * i + 2 < size → data i ≤ data (2 * i + 2))

/-- The minimum element is at index 0. -/
private theorem minHeap_root_is_min_aux (data : Nat → Nat) (size : Nat)
    (h_heap : isMinHeap data size) (h_pos : size > 0) :
    ∀ n i, i < size → i ≤ n → data 0 ≤ data i := by
  intro n
  induction n with
  | zero =>
    intro i h_i_lt h_le
    have : i = 0 := by omega
    subst this; exact Nat.le_refl _
  | succ n ih =>
    intro i h_i_lt h_le
    match i with
    | 0 => exact Nat.le_refl _
    | i + 1 =>
      -- parent of (i+1) is i / 2, and i / 2 ≤ n since i + 1 ≤ n + 1
      have h_parent_le_n : i / 2 ≤ n := by omega
      have h_parent_lt_size : i / 2 < size := by omega
      have h_root_le_parent := ih (i / 2) h_parent_lt_size h_parent_le_n
      have h_heap_parent := h_heap (i / 2) h_parent_lt_size
      by_cases h_odd : i + 1 = 2 * (i / 2) + 1
      · have h_le := h_heap_parent.1 (by omega : 2 * (i / 2) + 1 < size)
        calc data 0 ≤ data (i / 2) := h_root_le_parent
          _ ≤ data (2 * (i / 2) + 1) := h_le
          _ = data (i + 1) := by rw [h_odd]
      · have h_even : i + 1 = 2 * (i / 2) + 2 := by omega
        have h_le := h_heap_parent.2 (by omega : 2 * (i / 2) + 2 < size)
        calc data 0 ≤ data (i / 2) := h_root_le_parent
          _ ≤ data (2 * (i / 2) + 2) := h_le
          _ = data (i + 1) := by rw [h_even]

theorem minHeap_root_is_min (data : Nat → Nat) (size : Nat)
    (h_heap : isMinHeap data size) (h_pos : size > 0) :
    ∀ i, i < size → data 0 ≤ data i :=
  fun i h => minHeap_root_is_min_aux data size h_heap h_pos i i h (Nat.le_refl _)

/-! # Step 4: FuncSpecs -/

/-- pq_init: initializes empty queue. -/
def pq_init_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.pq
  post := fun r s =>
    r = Except.ok () →
    let pq := hVal s.globals.rawHeap s.locals.pq
    pq.size = 0 ∧ pq.capacity = s.locals.capacity

/-- pq_size: returns current size. -/
def pq_size_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.pq
  post := fun r s =>
    r = Except.ok () →
    s.locals.ret__val = (hVal s.globals.rawHeap s.locals.pq).size

/-- pq_is_empty: checks size == 0. -/
def pq_is_empty_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.pq
  post := fun r s =>
    r = Except.ok () →
    let pq := hVal s.globals.rawHeap s.locals.pq
    (pq.size = 0 → s.locals.ret__val = 1) ∧
    (pq.size ≠ 0 → s.locals.ret__val = 0)

/-- pq_is_full: checks size >= capacity. -/
def pq_is_full_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.pq
  post := fun r s =>
    r = Except.ok () →
    let pq := hVal s.globals.rawHeap s.locals.pq
    (pq.size >= pq.capacity → s.locals.ret__val = 1) ∧
    (pq.size < pq.capacity → s.locals.ret__val = 0)

/-- pq_insert: adds element, maintains heap property.
    Returns 0 on success, 1 if full. -/
def pq_insert_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.pq ∧
    (hVal s.globals.rawHeap s.locals.pq).size <
      (hVal s.globals.rawHeap s.locals.pq).capacity
  post := fun r s =>
    r = Except.ok () →
    s.locals.ret__val = 0

/-- pq_extract_min: removes and returns minimum element.
    Returns 0 on success, 1 if empty. -/
def pq_extract_min_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.pq ∧
    heapPtrValid s.globals.rawHeap s.locals.out ∧
    (hVal s.globals.rawHeap s.locals.pq).size > 0
  post := fun r s =>
    r = Except.ok () →
    s.locals.ret__val = 0

/-! # Step 5: validHoare theorems -/

-- Helper: heapUpdate preserves heapPtrValid at same pointer for C_pqueue
private theorem pq_heapUpdate_pq_ptrValid (s : ProgramState)
    (hv : heapPtrValid s.globals.rawHeap s.locals.pq)
    (v : PriorityQueue.C_pqueue) :
    heapPtrValid (heapUpdate s.globals.rawHeap s.locals.pq v) s.locals.pq :=
  heapUpdate_preserves_heapPtrValid _ _ _ _ hv

theorem pq_init_correct :
    pq_init_spec.satisfiedBy PriorityQueue.l1_pq_init_body := by
  unfold FuncSpec.satisfiedBy pq_init_spec validHoare
  intro s hpre
  -- L1 body: catch (seq (seq guard modify_size) (seq guard modify_cap)) skip
  let p := fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.pq
  let f1 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.pq ({ hVal s.globals.rawHeap s.locals.pq with size := 0 } : PriorityQueue.C_pqueue) } }
  let f2 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.pq ({ hVal s.globals.rawHeap s.locals.pq with capacity := s.locals.capacity } : PriorityQueue.C_pqueue) } }
  let s1 := f1 s
  let s2 := f2 s1
  -- heapPtrValid preservation
  have hv1 : p s1 := pq_heapUpdate_pq_ptrValid s hpre _
  -- Step results
  have h1 := L1_guard_modify_result p f1 s hpre
  have h2 := L1_guard_modify_result p f2 s1 hv1
  -- Chain steps 1,2
  have h12 := L1_seq_singleton_ok h1.1 h1.2 (m₂ := L1.seq (L1.guard p) (L1.modify f2))
  have h12_res : (L1.seq (L1.seq (L1.guard p) (L1.modify f1)) (L1.seq (L1.guard p) (L1.modify f2)) s).results = {(Except.ok (), s2)} := by
    rw [h12.1, h2.1]
  have h12_nf : ¬(L1.seq (L1.seq (L1.guard p) (L1.modify f1)) (L1.seq (L1.guard p) (L1.modify f2)) s).failed :=
    fun hf => h2.2 (h12.2.mp hf)
  -- Catch wrapper
  have h_catch := L1_catch_singleton_ok h12_res h12_nf
  unfold PriorityQueue.l1_pq_init_body
  constructor
  · exact h_catch.2
  · intro r s' h_mem
    rw [h_catch.1] at h_mem
    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
    subst hr; subst hs
    intro _
    -- Postcondition: hVal at s2 has size=0 and capacity=s.locals.capacity
    have hb := heapPtrValid_bound hpre
    have hb1 := heapPtrValid_bound hv1
    have h2v : hVal s2.globals.rawHeap s2.locals.pq =
        ({ hVal s1.globals.rawHeap s1.locals.pq with capacity := s.locals.capacity } : PriorityQueue.C_pqueue) :=
      hVal_heapUpdate_same _ _ _ hb1
    have h1v : hVal s1.globals.rawHeap s1.locals.pq =
        ({ hVal s.globals.rawHeap s.locals.pq with size := 0 } : PriorityQueue.C_pqueue) :=
      hVal_heapUpdate_same _ _ _ hb
    rw [h2v, h1v]
    exact ⟨rfl, rfl⟩

private theorem pq_retval_globals (s : ProgramState) (v : UInt32) :
    ({ s with locals := { s.locals with ret__val := v } } : ProgramState).globals = s.globals := rfl
private theorem pq_retval_pq (s : ProgramState) (v : UInt32) :
    ({ s with locals := { s.locals with ret__val := v } } : ProgramState).locals.pq = s.locals.pq := rfl
private theorem pq_retval_val (s : ProgramState) (v : UInt32) :
    ({ s with locals := { s.locals with ret__val := v } } : ProgramState).locals.ret__val = v := rfl

attribute [local irreducible] hVal heapPtrValid in
theorem pq_size_correct :
    pq_size_spec.satisfiedBy PriorityQueue.l1_pq_size_body := by
  unfold FuncSpec.satisfiedBy pq_size_spec validHoare
  intro s hpre
  unfold PriorityQueue.l1_pq_size_body
  have h := L1_guard_modify_throw_catch_skip_result
    (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.pq)
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := (hVal s.globals.rawHeap s.locals.pq).size } })
    s hpre
  obtain ⟨h_res, h_nf⟩ := h
  constructor
  · exact h_nf
  · intro r s' h_mem _
    rw [h_res] at h_mem
    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
    subst hr; subst hs
    rw [pq_retval_val, pq_retval_globals, pq_retval_pq]

-- pq_is_empty has the same guard-modify-throw-catch-skip pattern as pq_size,
-- but the modify function includes an if-then-else on (hVal ...).size == 0.
-- The 16-field PriorityQueue.Locals struct causes kernel deep recursion when
-- substituting the full modified state. Work around by NOT substituting s'.
attribute [local irreducible] hVal heapPtrValid in
theorem pq_is_empty_correct :
    pq_is_empty_spec.satisfiedBy PriorityQueue.l1_pq_is_empty_body := by
  unfold FuncSpec.satisfiedBy pq_is_empty_spec validHoare
  intro s hpre
  unfold PriorityQueue.l1_pq_is_empty_body
  have h := L1_guard_modify_throw_catch_skip_result
    (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.pq)
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := (if (hVal s.globals.rawHeap s.locals.pq).size == 0 then 1 else 0) } })
    s hpre
  obtain ⟨h_res, h_nf⟩ := h
  refine ⟨h_nf, fun r s' h_mem _ => ?_⟩
  rw [h_res] at h_mem
  have ⟨hr, hs⟩ := Prod.mk.inj h_mem
  subst hr
  -- s' = modified state. Don't subst hs to avoid kernel deep recursion.
  -- Instead, prove via projection through hs.
  have h_rv : s'.locals.ret__val = (if (hVal s.globals.rawHeap s.locals.pq).size == 0 then 1 else 0) :=
    hs ▸ pq_retval_val s _
  have h_gl : s'.globals = s.globals :=
    hs ▸ pq_retval_globals s _
  have h_pq : s'.locals.pq = s.locals.pq :=
    hs ▸ pq_retval_pq s _
  rw [h_gl, h_pq]
  constructor
  · intro h_zero; rw [h_rv, beq_iff_eq.mpr h_zero]; rfl
  · intro h_nz; rw [h_rv, beq_eq_false_iff_ne.mpr h_nz]; rfl

-- requires inter-procedural call resolution (pq_bubble_up) not yet supported
theorem pq_insert_correct :
    pq_insert_spec.satisfiedBy PriorityQueue.l1_pq_insert_body := by
  sorry -- requires call resolution for pq_bubble_up

-- requires inter-procedural call resolution (pq_bubble_down) not yet supported
theorem pq_extract_min_correct :
    pq_extract_min_spec.satisfiedBy PriorityQueue.l1_pq_extract_min_body := by
  sorry -- requires call resolution for pq_bubble_down

/-! # Step 6: Array bounds (task 0186)

The priority queue exercises array subscript at:
- pq_swap: data[i], data[j]
- pq_bubble_up: data[i], data[parent] where parent = (i-1)/2
- pq_bubble_down: data[i], data[left], data[right]
- pq_insert: data[pq->size]
- pq_extract_min: data[0], data[pq->size]

Bounds guards needed:
- pq_swap: i < capacity ∧ j < capacity
- pq_bubble_up: i < size (parent < i < size)
- pq_bubble_down: i < size (left, right checked explicitly)
- pq_insert: size < capacity (checked by guard)
- pq_extract_min: size > 0 (checked by guard)

The key insight: if size <= capacity and all heap operations
maintain size correctly, all array accesses are in bounds. -/

/-- Parent index is always less than child. -/
theorem parent_lt_child (i : Nat) (h : i > 0) : (i - 1) / 2 < i := by
  omega

/-- Left child index formula. -/
theorem left_child_gt (i : Nat) : i < 2 * i + 1 := by omega

/-- Right child index formula. -/
theorem right_child_gt (i : Nat) : i < 2 * i + 2 := by omega
