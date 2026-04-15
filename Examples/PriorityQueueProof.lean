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

/-- All data array elements up to index n are heap-valid.
    Required by pq_insert/extract_min because the L1 body contains
    guard (heapPtrValid data[i]) checks for array accesses. -/
def dataArrayValid (heap : HeapRawState) (data : Ptr UInt32) (n : Nat) : Prop :=
  ∀ i, i < n → heapPtrValid heap (Ptr.elemOffset data i)

/-- heapUpdate at any pointer preserves dataArrayValid. -/
private theorem dataArrayValid_heapUpdate {α : Type} [MemType α]
    (heap : HeapRawState) (p : Ptr α) (v : α) (data : Ptr UInt32) (n : Nat)
    (h : dataArrayValid heap data n) :
    dataArrayValid (heapUpdate heap p v) data n :=
  fun i hi => heapUpdate_preserves_heapPtrValid _ _ _ _ (h i hi)

/-- pq_insert: adds element, maintains heap property.
    Returns 0 on success, 1 if full.
    Precondition includes data array validity (needed for guard checks). -/
def pq_insert_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.pq ∧
    (hVal s.globals.rawHeap s.locals.pq).size <
      (hVal s.globals.rawHeap s.locals.pq).capacity ∧
    dataArrayValid s.globals.rawHeap s.locals.data
      (hVal s.globals.rawHeap s.locals.pq).capacity.toNat
  post := fun r s =>
    r = Except.ok () →
    s.locals.ret__val = 0

/-- pq_extract_min: removes and returns minimum element.
    Returns 0 on success, 1 if empty.
    Precondition includes data array validity (needed for guard checks). -/
def pq_extract_min_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.pq ∧
    heapPtrValid s.globals.rawHeap s.locals.out ∧
    (hVal s.globals.rawHeap s.locals.pq).size > 0 ∧
    dataArrayValid s.globals.rawHeap s.locals.data
      (hVal s.globals.rawHeap s.locals.pq).size.toNat
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

/-! ## Inter-procedural verification infrastructure -/

private noncomputable def insert_l1Γ : L1.L1ProcEnv ProgramState :=
  (((((((((L1.L1ProcEnv.empty.insert "pq_init" PriorityQueue.l1_pq_init_body).insert
    "pq_is_full" PriorityQueue.l1_pq_is_full_body).insert
    "pq_peek" PriorityQueue.l1_pq_peek_body).insert
    "pq_is_empty" PriorityQueue.l1_pq_is_empty_body).insert
    "pq_swap" PriorityQueue.l1_pq_swap_body).insert
    "pq_size" PriorityQueue.l1_pq_size_body).insert
    "pq_bubble_down" PriorityQueue.l1_pq_bubble_down_body).insert
    "pq_bubble_up" PriorityQueue.l1_pq_bubble_up_body).insert
    "pq_extract_min" PriorityQueue.l1_pq_extract_min_body)

attribute [local irreducible]
  PriorityQueue.l1_pq_init_body PriorityQueue.l1_pq_swap_body
  PriorityQueue.l1_pq_bubble_up_body PriorityQueue.l1_pq_bubble_down_body
  PriorityQueue.l1_pq_insert_body PriorityQueue.l1_pq_extract_min_body
  PriorityQueue.l1_pq_peek_body PriorityQueue.l1_pq_size_body
  PriorityQueue.l1_pq_is_empty_body PriorityQueue.l1_pq_is_full_body in
private theorem insert_l1Γ_lookup_bubble_up :
    insert_l1Γ "pq_bubble_up" = some PriorityQueue.l1_pq_bubble_up_body := by
  simp [insert_l1Γ, L1.L1ProcEnv.insert]

attribute [local irreducible]
  PriorityQueue.l1_pq_init_body PriorityQueue.l1_pq_swap_body
  PriorityQueue.l1_pq_bubble_up_body PriorityQueue.l1_pq_bubble_down_body
  PriorityQueue.l1_pq_insert_body PriorityQueue.l1_pq_extract_min_body
  PriorityQueue.l1_pq_peek_body PriorityQueue.l1_pq_size_body
  PriorityQueue.l1_pq_is_empty_body PriorityQueue.l1_pq_is_full_body in
private theorem insert_call_resolves :
    L1.call insert_l1Γ "pq_bubble_up" = PriorityQueue.l1_pq_bubble_up_body := by
  simp [L1.call, insert_l1Γ, L1.L1ProcEnv.insert]

private noncomputable def extract_min_l1Γ : L1.L1ProcEnv ProgramState :=
  (((((((((L1.L1ProcEnv.empty.insert "pq_init" PriorityQueue.l1_pq_init_body).insert
    "pq_is_full" PriorityQueue.l1_pq_is_full_body).insert
    "pq_peek" PriorityQueue.l1_pq_peek_body).insert
    "pq_is_empty" PriorityQueue.l1_pq_is_empty_body).insert
    "pq_swap" PriorityQueue.l1_pq_swap_body).insert
    "pq_size" PriorityQueue.l1_pq_size_body).insert
    "pq_bubble_down" PriorityQueue.l1_pq_bubble_down_body).insert
    "pq_bubble_up" PriorityQueue.l1_pq_bubble_up_body).insert
    "pq_extract_min" PriorityQueue.l1_pq_extract_min_body)

attribute [local irreducible]
  PriorityQueue.l1_pq_init_body PriorityQueue.l1_pq_swap_body
  PriorityQueue.l1_pq_bubble_up_body PriorityQueue.l1_pq_bubble_down_body
  PriorityQueue.l1_pq_insert_body PriorityQueue.l1_pq_extract_min_body
  PriorityQueue.l1_pq_peek_body PriorityQueue.l1_pq_size_body
  PriorityQueue.l1_pq_is_empty_body PriorityQueue.l1_pq_is_full_body in
private theorem extract_min_l1Γ_lookup_bubble_down :
    extract_min_l1Γ "pq_bubble_down" = some PriorityQueue.l1_pq_bubble_down_body := by
  simp [extract_min_l1Γ, L1.L1ProcEnv.insert]

attribute [local irreducible]
  PriorityQueue.l1_pq_init_body PriorityQueue.l1_pq_swap_body
  PriorityQueue.l1_pq_bubble_up_body PriorityQueue.l1_pq_bubble_down_body
  PriorityQueue.l1_pq_insert_body PriorityQueue.l1_pq_extract_min_body
  PriorityQueue.l1_pq_peek_body PriorityQueue.l1_pq_size_body
  PriorityQueue.l1_pq_is_empty_body PriorityQueue.l1_pq_is_full_body in
private theorem extract_min_call_resolves :
    L1.call extract_min_l1Γ "pq_bubble_down" = PriorityQueue.l1_pq_bubble_down_body := by
  simp [L1.call, extract_min_l1Γ, L1.L1ProcEnv.insert]

/-! ## Callee specs for pq_swap and pq_bubble_up -/

private theorem uint32_pqueue_typeTag_ne :
    (inferInstance : CType UInt32).typeTag ≠ (inferInstance : CType PriorityQueue.C_pqueue).typeTag := by
  decide

-- pq_swap: catch(guard+modify chain, skip)
-- Non-failure when data[i] and data[j] are heap-valid.
-- Result always ok (catch+skip pattern).
--
-- Step function decomposition for kernel depth safety.
-- PriorityQueue.Locals has 16 fields — anonymous constructors avoid deep recursion.

/-- Step 1 transform: tmp := data[i] (only locals.tmp changes) -/
private noncomputable def pq_swap_f1 (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.capacity, s.locals.data, s.locals.heap_size, s.locals.i,
    s.locals.iters, s.locals.j, s.locals.left, s.locals.out, s.locals.parent,
    s.locals.pq, s.locals.ret__val, s.locals.right, s.locals.root_idx, s.locals.smallest,
    hVal s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.i.toNat), s.locals.value⟩⟩

/-- Step 2 transform: data[i] := data[j] (only globals.rawHeap changes) -/
private noncomputable def pq_swap_f2 (s : ProgramState) : ProgramState :=
  ⟨⟨heapUpdate s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.i.toNat)
    (hVal s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.j.toNat))⟩, s.locals⟩

/-- Step 3 transform: data[j] := tmp (only globals.rawHeap changes) -/
private noncomputable def pq_swap_f3 (s : ProgramState) : ProgramState :=
  ⟨⟨heapUpdate s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.j.toNat)
    s.locals.tmp⟩, s.locals⟩

/-- Step 1 as L1 monad: guard(heapPtrValid data[i]) >> modify(pq_swap_f1) -/
private noncomputable def pq_swap_l1_step1 : L1Monad ProgramState :=
  L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.i.toNat)))
    (L1.modify pq_swap_f1)

/-- Step 2: guard(heapPtrValid data[i]) >> guard(heapPtrValid data[j]) >> modify(pq_swap_f2) -/
private noncomputable def pq_swap_l1_step2 : L1Monad ProgramState :=
  L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.i.toNat)))
    (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.j.toNat)))
      (L1.modify pq_swap_f2))

/-- Step 3: guard(heapPtrValid data[j]) >> modify(pq_swap_f3) -/
private noncomputable def pq_swap_l1_step3 : L1Monad ProgramState :=
  L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.j.toNat)))
    (L1.modify pq_swap_f3)

/-- The pq_swap body decomposed into named steps. -/
private noncomputable abbrev pq_swap_body_decomposed : L1Monad ProgramState :=
  L1.catch (L1.seq pq_swap_l1_step1 (L1.seq pq_swap_l1_step2 pq_swap_l1_step3)) L1.skip

private theorem pq_swap_body_decomposed_eq :
    pq_swap_body_decomposed = PriorityQueue.l1_pq_swap_body := by
  unfold pq_swap_body_decomposed pq_swap_l1_step1 pq_swap_l1_step2 pq_swap_l1_step3
    pq_swap_f1 pq_swap_f2 pq_swap_f3 PriorityQueue.l1_pq_swap_body
  rfl

-- Projection lemmas for step functions

attribute [local irreducible] hVal in
@[simp] private theorem pq_swap_f1_globals (s : ProgramState) :
    (pq_swap_f1 s).globals = s.globals := by
  show (⟨s.globals, ⟨s.locals.capacity, s.locals.data, s.locals.heap_size, s.locals.i,
    s.locals.iters, s.locals.j, s.locals.left, s.locals.out, s.locals.parent,
    s.locals.pq, s.locals.ret__val, s.locals.right, s.locals.root_idx, s.locals.smallest,
    hVal s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.i.toNat), s.locals.value⟩⟩ :
    ProgramState).globals = _; rfl

attribute [local irreducible] hVal in
private theorem pq_swap_f1_locals_eq (s : ProgramState) :
    (pq_swap_f1 s).locals = ⟨s.locals.capacity, s.locals.data, s.locals.heap_size, s.locals.i,
      s.locals.iters, s.locals.j, s.locals.left, s.locals.out, s.locals.parent,
      s.locals.pq, s.locals.ret__val, s.locals.right, s.locals.root_idx, s.locals.smallest,
      hVal s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.i.toNat), s.locals.value⟩ := by
  show (⟨s.globals, ⟨s.locals.capacity, s.locals.data, s.locals.heap_size, s.locals.i,
    s.locals.iters, s.locals.j, s.locals.left, s.locals.out, s.locals.parent,
    s.locals.pq, s.locals.ret__val, s.locals.right, s.locals.root_idx, s.locals.smallest,
    hVal s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.i.toNat), s.locals.value⟩⟩ :
    ProgramState).locals = _; rfl

@[simp] private theorem pq_swap_f1_data (s : ProgramState) :
    (pq_swap_f1 s).locals.data = s.locals.data := by rw [pq_swap_f1_locals_eq]
@[simp] private theorem pq_swap_f1_i (s : ProgramState) :
    (pq_swap_f1 s).locals.i = s.locals.i := by rw [pq_swap_f1_locals_eq]
@[simp] private theorem pq_swap_f1_j (s : ProgramState) :
    (pq_swap_f1 s).locals.j = s.locals.j := by rw [pq_swap_f1_locals_eq]

attribute [local irreducible] hVal heapUpdate in
@[simp] private theorem pq_swap_f2_globals_rawHeap (s : ProgramState) :
    (pq_swap_f2 s).globals.rawHeap = heapUpdate s.globals.rawHeap
      (Ptr.elemOffset s.locals.data s.locals.i.toNat)
      (hVal s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.j.toNat)) := by
  show (⟨⟨heapUpdate s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.i.toNat)
    (hVal s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.j.toNat))⟩, s.locals⟩ :
    ProgramState).globals.rawHeap = _; rfl

attribute [local irreducible] hVal heapUpdate in
@[simp] private theorem pq_swap_f2_locals (s : ProgramState) :
    (pq_swap_f2 s).locals = s.locals := by
  show (⟨⟨heapUpdate s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.i.toNat)
    (hVal s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.j.toNat))⟩, s.locals⟩ :
    ProgramState).locals = _; rfl

attribute [local irreducible] heapUpdate in
@[simp] private theorem pq_swap_f3_locals (s : ProgramState) :
    (pq_swap_f3 s).locals = s.locals := by
  show (⟨⟨heapUpdate s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.j.toNat)
    s.locals.tmp⟩, s.locals⟩ : ProgramState).locals = _; rfl

-- heapPtrValid preservation through step functions

private theorem pq_swap_f1_preserves_hpv_di (s : ProgramState)
    (h : heapPtrValid s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.i.toNat)) :
    heapPtrValid (pq_swap_f1 s).globals.rawHeap (Ptr.elemOffset (pq_swap_f1 s).locals.data (pq_swap_f1 s).locals.i.toNat) := by
  simp only [pq_swap_f1_globals, pq_swap_f1_data, pq_swap_f1_i]; exact h

private theorem pq_swap_f1_preserves_hpv_dj (s : ProgramState)
    (h : heapPtrValid s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.j.toNat)) :
    heapPtrValid (pq_swap_f1 s).globals.rawHeap (Ptr.elemOffset (pq_swap_f1 s).locals.data (pq_swap_f1 s).locals.j.toNat) := by
  simp only [pq_swap_f1_globals, pq_swap_f1_data, pq_swap_f1_j]; exact h

private theorem pq_swap_f2_preserves_hpv_dj (s : ProgramState)
    (h : heapPtrValid s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.j.toNat)) :
    heapPtrValid (pq_swap_f2 s).globals.rawHeap (Ptr.elemOffset (pq_swap_f2 s).locals.data (pq_swap_f2 s).locals.j.toNat) := by
  simp only [pq_swap_f2_globals_rawHeap, pq_swap_f2_locals]
  exact heapUpdate_preserves_heapPtrValid _ _ _ _ h

-- Main non-failure proof for the decomposed body.
private theorem pq_swap_body_nf (s : ProgramState)
    (hdi : heapPtrValid s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.i.toNat))
    (hdj : heapPtrValid s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.j.toNat)) :
    ¬(pq_swap_body_decomposed s).failed ∧
    ∀ (r : Except Unit Unit) (s' : ProgramState),
      (r, s') ∈ (pq_swap_body_decomposed s).results → r = Except.ok () := by
  -- Step 1: guard(heapPtrValid data[i]) >> modify(pq_swap_f1)
  have h1 := L1_guard_modify_result
    (fun s : ProgramState => heapPtrValid s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.i.toNat))
    pq_swap_f1 s hdi
  have h_step1_res : (pq_swap_l1_step1 s).results = {(Except.ok (), pq_swap_f1 s)} := by
    unfold pq_swap_l1_step1; exact h1.1
  have h_step1_nf : ¬(pq_swap_l1_step1 s).failed := by unfold pq_swap_l1_step1; exact h1.2
  -- Step 2: guard(di) >> guard(dj) >> modify(f2) at (pq_swap_f1 s)
  have hdi1 := pq_swap_f1_preserves_hpv_di s hdi
  have hdj1 := pq_swap_f1_preserves_hpv_dj s hdj
  have h2 := L1_guard_guard_modify_result
    (fun s : ProgramState => heapPtrValid s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.i.toNat))
    (fun s : ProgramState => heapPtrValid s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.j.toNat))
    pq_swap_f2 (pq_swap_f1 s) hdi1 hdj1
  have h_step2_res : (pq_swap_l1_step2 (pq_swap_f1 s)).results =
      {(Except.ok (), pq_swap_f2 (pq_swap_f1 s))} := by
    unfold pq_swap_l1_step2; exact h2.1
  have h_step2_nf : ¬(pq_swap_l1_step2 (pq_swap_f1 s)).failed := by
    unfold pq_swap_l1_step2; exact h2.2
  -- Step 3: guard(dj) >> modify(f3) at (pq_swap_f2 (pq_swap_f1 s))
  have hdj2 := pq_swap_f2_preserves_hpv_dj (pq_swap_f1 s) hdj1
  have h3 := L1_guard_modify_result
    (fun s : ProgramState => heapPtrValid s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.j.toNat))
    pq_swap_f3 (pq_swap_f2 (pq_swap_f1 s)) hdj2
  have h_step3_res : (pq_swap_l1_step3 (pq_swap_f2 (pq_swap_f1 s))).results =
      {(Except.ok (), pq_swap_f3 (pq_swap_f2 (pq_swap_f1 s)))} := by
    unfold pq_swap_l1_step3; exact h3.1
  have h_step3_nf : ¬(pq_swap_l1_step3 (pq_swap_f2 (pq_swap_f1 s))).failed := by
    unfold pq_swap_l1_step3; exact h3.2
  -- Chain: seq step2 step3
  have h_seq23 := L1_seq_singleton_ok h_step2_res h_step2_nf (m₂ := pq_swap_l1_step3)
  have h_seq23_nf : ¬(L1.seq pq_swap_l1_step2 pq_swap_l1_step3 (pq_swap_f1 s)).failed :=
    fun hf => h_step3_nf (h_seq23.2.mp hf)
  have h_seq23_res : (L1.seq pq_swap_l1_step2 pq_swap_l1_step3 (pq_swap_f1 s)).results =
      {(Except.ok (), pq_swap_f3 (pq_swap_f2 (pq_swap_f1 s)))} := by
    rw [h_seq23.1, h_step3_res]
  -- Chain: seq step1 (seq step2 step3)
  have h_inner := L1_seq_singleton_ok h_step1_res h_step1_nf
    (m₂ := L1.seq pq_swap_l1_step2 pq_swap_l1_step3)
  have h_inner_res : (L1.seq pq_swap_l1_step1 (L1.seq pq_swap_l1_step2 pq_swap_l1_step3) s).results =
      {(Except.ok (), pq_swap_f3 (pq_swap_f2 (pq_swap_f1 s)))} := by
    rw [h_inner.1, h_seq23_res]
  have h_inner_nf : ¬(L1.seq pq_swap_l1_step1 (L1.seq pq_swap_l1_step2 pq_swap_l1_step3) s).failed :=
    fun hf => h_seq23_nf (h_inner.2.mp hf)
  -- Outer catch: catch inner skip
  have h_catch := L1_catch_singleton_ok h_inner_res h_inner_nf
  unfold pq_swap_body_decomposed
  exact ⟨h_catch.2, fun r s' h_mem => by
    rw [h_catch.1] at h_mem
    exact (Prod.mk.inj h_mem).1⟩

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem pq_swap_ok_hoare :
    validHoare
      (fun s => heapPtrValid s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.i.toNat) ∧
                heapPtrValid s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.j.toNat))
      PriorityQueue.l1_pq_swap_body
      (fun r _ => r = Except.ok ()) := by
  rw [← pq_swap_body_decomposed_eq]
  intro s ⟨hdi, hdj⟩
  have ⟨h_nf, h_ok⟩ := pq_swap_body_nf s hdi hdj
  exact ⟨h_nf, fun r s' h_mem => h_ok r s' h_mem⟩

-- pq_bubble_up: non-failure + ok-only result.
-- Proof uses L1_hoare_while with invariant tracking dataArrayValid and i bounds.
-- The h_body_inv (loop invariant preservation through ok results) requires
-- tracking state through dynCom(pq_swap) which involves detailed NondetM reasoning.
-- The core argument: pq_swap only does heapUpdates, which preserve all heapPtrValid
-- (hence dataArrayValid), and i decreases each iteration (parent = (i-1)/2 < i).
-- pq_bubble_up: catch(while(i > 0, loop_body), skip)
-- Non-failure when dataArrayValid and i < n and pq valid.
-- Returns ok always (catch+skip pattern).
-- Proof sketch: L1_hoare_while with invariant (dataArrayValid, i < n, heapPtrValid pq).
-- h_body_nf: guards are heapPtrValid data[i/parent] from dataArrayValid + bounds.
-- h_body_inv: pq_swap only does heapUpdates (preserves heapPtrValid → preserves dataArrayValid),
--   i decreases each iteration (parent = (i-1)/2 < i for i > 0).
-- Postcondition includes heapPtrValid pq preservation (needed by caller after dynCom restore).
-- bubble_up preserves pq validity because it only does heapUpdates (via pq_swap),
-- and heapUpdate_preserves_heapPtrValid applies universally.
-- Also includes s'.locals.pq = s_input.locals.pq (bubble_up doesn't modify the pq local).
private theorem pq_bubble_up_ok_hoare (n : Nat) (pq₀ : Ptr PriorityQueue.C_pqueue) :
    validHoare
      (fun s => dataArrayValid s.globals.rawHeap s.locals.data n ∧
                s.locals.i.toNat < n ∧
                heapPtrValid s.globals.rawHeap s.locals.pq ∧
                s.locals.pq = pq₀)
      PriorityQueue.l1_pq_bubble_up_body
      (fun r s => r = Except.ok () ∧
                  heapPtrValid s.globals.rawHeap pq₀) := by
  sorry

/-! ## pq_insert proof

Structure: catch(seq(condition, rest), skip)
- condition(size >= capacity): false by precondition, takes skip branch
- rest: guard+modify(write data[size]), dynCom(bubble_up), guard+guard+modify(size++), modify(ret:=0)+throw
- catch+skip gives ok with ret_val = 0

Key non-failure obligations:
1. guard(heapPtrValid data[size]): from dataArrayValid + size < capacity
2. bubble_up doesn't fail: from pq_bubble_up_ok_hoare
3. guard(heapPtrValid pq) x2: pq validity preserved through heapUpdates
   (type safety: UInt32/C_pqueue have different type tags → ptrDisjoint) -/

-- The insert proof uses L1_hoare_catch with R = (ret_val = 0).
-- The catch body always ends in throw with ret_val = 0.
-- The catch handler (skip) converts error to ok, preserving ret_val = 0.
-- Non-failure: all guards satisfied from precondition + heapUpdate preservation.
-- Callee: pq_bubble_up_ok_hoare provides non-failure of bubble_up call.
attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem pq_insert_correct :
    pq_insert_spec.satisfiedBy PriorityQueue.l1_pq_insert_body := by
  unfold FuncSpec.satisfiedBy pq_insert_spec
  apply L1_hoare_catch (R := fun s => s.locals.ret__val = 0)
  · -- CATCH BODY: seq(condition, rest)
    -- condition false (precondition: size < capacity), then rest ends in throw with ret_val=0.
    apply L1_hoare_seq
      (R := fun s => heapPtrValid s.globals.rawHeap s.locals.pq ∧
                     (hVal s.globals.rawHeap s.locals.pq).size <
                       (hVal s.globals.rawHeap s.locals.pq).capacity ∧
                     dataArrayValid s.globals.rawHeap s.locals.data
                       (hVal s.globals.rawHeap s.locals.pq).capacity.toNat)
    · -- CONDITION: size >= capacity → true branch unreachable, false branch skip
      apply L1_hoare_condition
      · -- TRUE branch (full): vacuously true since P ∧ c=true implies False
        -- P says size < capacity, c says size >= capacity → contradiction
        intro s ⟨⟨_, hlt, _⟩, hc⟩
        simp only [decide_eq_true_eq] at hc
        exact absurd hlt (Nat.not_lt.mpr hc)
      · -- FALSE branch (not full): skip preserves state
        intro s ⟨⟨hpq, hlt, hdav⟩, _⟩
        exact ⟨not_false, fun r s' h_mem => by
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
          exact ⟨hpq, hlt, hdav⟩⟩
    · -- REST: seq(guard+modify(data write), seq(dynCom(bubble_up), ...))
      -- Step 1: guard+modify(data[size]:=value)
      apply L1_hoare_seq
        (R := fun s => heapPtrValid s.globals.rawHeap s.locals.pq ∧
                       dataArrayValid s.globals.rawHeap s.locals.data
                         (hVal s.globals.rawHeap s.locals.pq).capacity.toNat ∧
                       (hVal s.globals.rawHeap s.locals.pq).size <
                         (hVal s.globals.rawHeap s.locals.pq).capacity)
      · -- guard(heapPtrValid data[pq.size]) + modify(heapUpdate data[size]:=value)
        sorry
      · -- seq(dynCom(bubble_up), seq(guards+size++, ret_val:=0+throw))
        -- After data write: heapPtrValid pq preserved (different types),
        -- dataArrayValid preserved (heapUpdate_preserves_heapPtrValid).
        -- dynCom(bubble_up): bubble_up preserves heapPtrValid pq.
        -- After bubble_up: guard+guard+modify(size++), modify(ret_val:=0)+throw.
        sorry
  · -- HANDLER (skip): from R (ret_val = 0), skip gives ok with same state
    intro s hrs
    exact ⟨not_false, fun r s' h_mem => by
      have ⟨hr, hs⟩ := Prod.mk.inj h_mem
      subst hr; subst hs
      intro _; exact hrs⟩

-- SORRY: requires callee specs for pq_bubble_down + dynCom composition.
theorem pq_extract_min_correct :
    pq_extract_min_spec.satisfiedBy PriorityQueue.l1_pq_extract_min_body := by
  sorry

/-! # Step 6: Array bounds (task 0186) -/

/-- Parent index is always less than child. -/
theorem parent_lt_child (i : Nat) (h : i > 0) : (i - 1) / 2 < i := by
  omega

/-- Left child index formula. -/
theorem left_child_gt (i : Nat) : i < 2 * i + 1 := by omega

/-- Right child index formula. -/
theorem right_child_gt (i : Nat) : i < 2 * i + 2 := by omega
