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
theorem minHeap_root_is_min (data : Nat → Nat) (size : Nat)
    (h_heap : isMinHeap data size) (h_pos : size > 0) :
    ∀ i, i < size → data 0 ≤ data i := by
  -- This requires induction on the path from root to i
  sorry

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

theorem pq_init_correct :
    pq_init_spec.satisfiedBy PriorityQueue.l1_pq_init_body := by
  sorry

theorem pq_size_correct :
    pq_size_spec.satisfiedBy PriorityQueue.l1_pq_size_body := by
  sorry

theorem pq_is_empty_correct :
    pq_is_empty_spec.satisfiedBy PriorityQueue.l1_pq_is_empty_body := by
  sorry

theorem pq_insert_correct :
    pq_insert_spec.satisfiedBy PriorityQueue.l1_pq_insert_body := by
  sorry

theorem pq_extract_min_correct :
    pq_extract_min_spec.satisfiedBy PriorityQueue.l1_pq_extract_min_body := by
  sorry

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
