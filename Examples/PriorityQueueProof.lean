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

-- Stronger pq_swap spec: result = ok AND all heapPtrValid preserved.
-- Builds on pq_swap_body_nf (which computes the singleton result) and adds
-- heapPtrValid preservation through the 3 heapUpdate steps.
private theorem pq_swap_preserves_hpv (s : ProgramState)
    (hdi : heapPtrValid s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.i.toNat))
    (hdj : heapPtrValid s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.j.toNat)) :
    ∀ r s', (r, s') ∈ (PriorityQueue.l1_pq_swap_body s).results →
      r = Except.ok () ∧
      (∀ (α : Type) [inst : CType α] (p : Ptr α),
        @heapPtrValid α inst s.globals.rawHeap p → @heapPtrValid α inst s'.globals.rawHeap p) := by
  rw [← pq_swap_body_decomposed_eq]
  -- Reuse the existing decomposition to get the singleton result.
  -- Step results from pq_swap_body_nf's proof pattern:
  have h_step1_res : (pq_swap_l1_step1 s).results = {(Except.ok (), pq_swap_f1 s)} := by
    unfold pq_swap_l1_step1
    exact (L1_guard_modify_result _ pq_swap_f1 s hdi).1
  have h_step1_nf : ¬(pq_swap_l1_step1 s).failed := by
    unfold pq_swap_l1_step1
    exact (L1_guard_modify_result _ pq_swap_f1 s hdi).2
  have hdi1 := pq_swap_f1_preserves_hpv_di s hdi
  have hdj1 := pq_swap_f1_preserves_hpv_dj s hdj
  have h_step2_res : (pq_swap_l1_step2 (pq_swap_f1 s)).results =
      {(Except.ok (), pq_swap_f2 (pq_swap_f1 s))} := by
    unfold pq_swap_l1_step2
    exact (L1_guard_guard_modify_result _ _ pq_swap_f2 (pq_swap_f1 s) hdi1 hdj1).1
  have h_step2_nf : ¬(pq_swap_l1_step2 (pq_swap_f1 s)).failed := by
    unfold pq_swap_l1_step2
    exact (L1_guard_guard_modify_result _ _ pq_swap_f2 (pq_swap_f1 s) hdi1 hdj1).2
  have hdj2 := pq_swap_f2_preserves_hpv_dj (pq_swap_f1 s) hdj1
  have h_step3_res : (pq_swap_l1_step3 (pq_swap_f2 (pq_swap_f1 s))).results =
      {(Except.ok (), pq_swap_f3 (pq_swap_f2 (pq_swap_f1 s)))} := by
    unfold pq_swap_l1_step3
    exact (L1_guard_modify_result _ pq_swap_f3 (pq_swap_f2 (pq_swap_f1 s)) hdj2).1
  have h_step3_nf : ¬(pq_swap_l1_step3 (pq_swap_f2 (pq_swap_f1 s))).failed := by
    unfold pq_swap_l1_step3
    exact (L1_guard_modify_result _ pq_swap_f3 (pq_swap_f2 (pq_swap_f1 s)) hdj2).2
  -- Chain
  have h_seq23 := L1_seq_singleton_ok h_step2_res h_step2_nf (m₂ := pq_swap_l1_step3)
  have h_seq23_res : (L1.seq pq_swap_l1_step2 pq_swap_l1_step3 (pq_swap_f1 s)).results =
      {(Except.ok (), pq_swap_f3 (pq_swap_f2 (pq_swap_f1 s)))} := by
    rw [h_seq23.1, h_step3_res]
  have h_seq23_nf : ¬(L1.seq pq_swap_l1_step2 pq_swap_l1_step3 (pq_swap_f1 s)).failed :=
    fun hf => h_step3_nf (h_seq23.2.mp hf)
  have h_inner := L1_seq_singleton_ok h_step1_res h_step1_nf
    (m₂ := L1.seq pq_swap_l1_step2 pq_swap_l1_step3)
  have h_inner_res : (L1.seq pq_swap_l1_step1 (L1.seq pq_swap_l1_step2 pq_swap_l1_step3) s).results =
      {(Except.ok (), pq_swap_f3 (pq_swap_f2 (pq_swap_f1 s)))} := by
    rw [h_inner.1, h_seq23_res]
  have h_inner_nf : ¬(L1.seq pq_swap_l1_step1 (L1.seq pq_swap_l1_step2 pq_swap_l1_step3) s).failed :=
    fun hf => h_seq23_nf (h_inner.2.mp hf)
  have h_catch := L1_catch_singleton_ok h_inner_res h_inner_nf
  intro r s' h_mem
  unfold pq_swap_body_decomposed at h_mem
  rw [h_catch.1] at h_mem
  have ⟨hr, hs⟩ := Prod.mk.inj h_mem
  subst hr; subst hs
  refine ⟨rfl, fun α inst p hp => ?_⟩
  -- heapPtrValid preserved: f1 keeps globals, f2/f3 do heapUpdate
  have hg1 : (pq_swap_f1 s).globals = s.globals := pq_swap_f1_globals s
  exact heapUpdate_preserves_heapPtrValid _ _ _ _
    (heapUpdate_preserves_heapPtrValid _ _ _ _
      (by rw [hg1]; exact hp))

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
-- NondetM-level helpers (same as HashTableProof but not private there)
private theorem pq_L1_seq_failed_iff (m₁ m₂ : L1Monad ProgramState) (s : ProgramState) :
    (L1.seq m₁ m₂ s).failed ↔
    ((m₁ s).failed ∨ ∃ s', (Except.ok (), s') ∈ (m₁ s).results ∧ (m₂ s').failed) :=
  Iff.rfl

private theorem pq_L1_seq_ok_mem {m₁ m₂ : L1Monad ProgramState} {s s' : ProgramState}
    (h : (Except.ok (), s') ∈ (L1.seq m₁ m₂ s).results) :
    ∃ s₁, (Except.ok (), s₁) ∈ (m₁ s).results ∧ (Except.ok (), s') ∈ (m₂ s₁).results := by
  change (_ ∨ _) at h
  rcases h with ⟨s₁, h₁, h₂⟩ | ⟨_, h_tag⟩
  · exact ⟨s₁, h₁, h₂⟩
  · exact absurd h_tag (by intro h; cases h)

private theorem pq_L1_seq_error_mem {m₁ m₂ : L1Monad ProgramState} {s s' : ProgramState}
    (h : (Except.error (), s') ∈ (L1.seq m₁ m₂ s).results) :
    (∃ s₁, (Except.ok (), s₁) ∈ (m₁ s).results ∧ (Except.error (), s') ∈ (m₂ s₁).results) ∨
    (Except.error (), s') ∈ (m₁ s).results := by
  change (_ ∨ _) at h
  rcases h with ⟨s₁, h₁, h₂⟩ | ⟨h_err, h_tag⟩
  · exact Or.inl ⟨s₁, h₁, h₂⟩
  · have : Except.error () = Except.error () := h_tag
    exact Or.inr h_err

-- Bridge: derive L1_hoare_while side-conditions from a single body Hoare proof.
private theorem pq_L1_hoare_while_from_body {c : ProgramState → Bool} {body : L1Monad ProgramState}
    {I : ProgramState → Prop} {Q : Except Unit Unit → ProgramState → Prop}
    (h_body : validHoare (fun s => I s ∧ c s = true) body
        (fun r s => match r with | Except.ok () => I s | Except.error () => Q (Except.error ()) s))
    (h_exit : ∀ s, I s → c s = false → Q (Except.ok ()) s) :
    validHoare I (L1.while c body) Q := by
  apply L1_hoare_while (I := I)
  · intro s h; exact h
  · intro s hi hc; exact (h_body s ⟨hi, hc⟩).1
  · intro s s' hi hc h_mem; exact (h_body s ⟨hi, hc⟩).2 (Except.ok ()) s' h_mem
  · exact h_exit
  · intro s s' hi hc h_mem; exact (h_body s ⟨hi, hc⟩).2 (Except.error ()) s' h_mem

-- UInt32 arithmetic: ((i - 1) / 2).toNat = (i.toNat - 1) / 2 when i > 0
private theorem uint32_parent_toNat_eq (i : UInt32) (h : i.toNat > 0) :
    ((i - 1) / 2).toNat = (i.toNat - 1) / 2 := by
  -- UInt32 is BitVec 32. Convert and use BitVec lemmas.
  show ((i.toBitVec - 1) / 2).toNat = (i.toBitVec.toNat - 1) / 2
  -- Sub: BitVec.toNat (a - b) = (a.toNat - b.toNat) % 2^32 when a ≥ b
  -- i.toBitVec.toNat > 0 and (1 : BitVec 32).toNat = 1
  -- So (i - 1).toNat = (i.toNat - 1) % 2^32 = i.toNat - 1 (since i.toNat ≤ 2^32 - 1)
  have h_bnd := i.toBitVec.isLt -- i.toNat < 2^32
  have h_sub : (i.toBitVec - 1).toNat = i.toBitVec.toNat - 1 := by
    rw [BitVec.toNat_sub]
    have h1 : (1 : BitVec 32).toNat = 1 := by decide
    rw [h1]
    -- Goal: (2^32 - 1 + i.toBitVec.toNat) % 2^32 = i.toBitVec.toNat - 1
    -- Rewrite: 2^32 - 1 + x = (x - 1) + 2^32 for x ≥ 1
    have h_pos : i.toBitVec.toNat > 0 := h
    have h_rw : 2^32 - 1 + i.toBitVec.toNat = (i.toBitVec.toNat - 1) + 2^32 := by omega
    rw [h_rw, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  -- Div: BitVec.toNat (a / b) = a.toNat / b.toNat (unsigned division)
  rw [show (2 : BitVec 32) = BitVec.ofNat 32 2 from rfl]
  rw [BitVec.toNat_udiv, h_sub]
  simp [BitVec.toNat_ofNat]

-- UInt32 arithmetic helper: (i - 1) / 2 < i for i > 0
private theorem uint32_parent_lt (i : UInt32) (h : i.toNat > 0) :
    ((i - 1) / 2).toNat < i.toNat := by
  rw [uint32_parent_toNat_eq i h]; omega

-- The bubble_up invariant.
private def bubble_up_inv (n : Nat) (pq₀ : Ptr PriorityQueue.C_pqueue) (s : ProgramState) : Prop :=
  dataArrayValid s.globals.rawHeap s.locals.data n ∧
  s.locals.i.toNat < n ∧
  heapPtrValid s.globals.rawHeap s.locals.pq ∧
  s.locals.pq = pq₀

private theorem pq_bubble_up_ok_hoare (n : Nat) (pq₀ : Ptr PriorityQueue.C_pqueue) :
    validHoare
      (fun s => dataArrayValid s.globals.rawHeap s.locals.data n ∧
                s.locals.i.toNat < n ∧
                heapPtrValid s.globals.rawHeap s.locals.pq ∧
                s.locals.pq = pq₀)
      PriorityQueue.l1_pq_bubble_up_body
      (fun r s => r = Except.ok () ∧
                  heapPtrValid s.globals.rawHeap pq₀) := by
  -- bubble_up = catch (while cond body) skip
  unfold PriorityQueue.l1_pq_bubble_up_body
  apply L1_hoare_catch (R := fun s => heapPtrValid s.globals.rawHeap pq₀)
  · -- While loop: validHoare P (while c body) (fun r s => match r | ok => Q ok s | error => R s)
    apply pq_L1_hoare_while_from_body
      (I := fun s => dataArrayValid s.globals.rawHeap s.locals.data n ∧
                     s.locals.i.toNat < n ∧
                     heapPtrValid s.globals.rawHeap s.locals.pq ∧
                     s.locals.pq = pq₀)
    · -- Body Hoare triple: I ∧ c=true → body → ok ⇒ I, error ⇒ heapPtrValid pq₀
      -- Body = seq (seq guard modify_parent) (condition ...)
      -- Step 1: guard(2≠0) + modify(parent := (i-1)/2)
      apply L1_hoare_seq_ok
        (R := fun s => dataArrayValid s.globals.rawHeap s.locals.data n ∧
                       s.locals.i.toNat < n ∧
                       heapPtrValid s.globals.rawHeap s.locals.pq ∧
                       s.locals.pq = pq₀ ∧
                       s.locals.i > 0 ∧
                       s.locals.parent = (s.locals.i - 1) / 2)
      · -- guard(2≠0) + modify(parent := (i-1)/2)
        intro s ⟨⟨hdav, hi_lt, hpq, hpq_eq⟩, hc⟩
        simp only [decide_eq_true_eq] at hc
        have h_guard : (2 : Nat) ≠ 0 := by omega
        have h_gm := L1_guard_modify_result (fun _ : ProgramState => (2 : Nat) ≠ 0)
          (fun s : ProgramState => { s with locals := { s.locals with parent := ((s.locals.i - 1) / 2) } })
          s h_guard
        exact ⟨h_gm.2, fun r s' h_mem => by
          rw [h_gm.1] at h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
          exact ⟨rfl, hdav, hi_lt, hpq, hpq_eq, hc, rfl⟩⟩
      · -- condition(data[i] < data[parent]): true → swap+advance, false → throw
        apply L1_hoare_condition
        · -- TRUE branch: data[i] < data[parent] → swap + i:=parent
          intro s ⟨⟨hdav, hi_lt, hpq, hpq_eq, hi_pos, h_parent⟩, _⟩
          have h_i_pos_nat : s.locals.i.toNat > 0 := by
            simp only [GT.gt, UInt32.lt_iff_toNat_lt] at hi_pos; exact hi_pos
          have h_parent_lt : s.locals.parent.toNat < n := by
            rw [h_parent]; exact Nat.lt_trans (uint32_parent_lt s.locals.i h_i_pos_nat) hi_lt
          have hdi : heapPtrValid s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.i.toNat) :=
            hdav s.locals.i.toNat hi_lt
          have hdp : heapPtrValid s.globals.rawHeap (Ptr.elemOffset s.locals.data s.locals.parent.toNat) :=
            hdav s.locals.parent.toNat h_parent_lt
          -- Seq(dynCom(swap), modify(i:=parent)):
          -- Prove using pq_swap_ok_hoare.
          -- The dynCom runs: setup(j:=parent), call pq_swap, restore(saved.locals).
          -- After restore + i_assign, invariant is preserved.
          --
          -- Key: pq_swap only does heapUpdates. So:
          -- - dataArrayValid preserved (heapUpdate_preserves_heapPtrValid)
          -- - heapPtrValid pq preserved (heapUpdate_preserves_heapPtrValid)
          -- - pq local unchanged (restore puts back saved.locals)
          -- - i becomes parent, parent.toNat < n
          --
          -- Resolve the L1.call by unfolding the env:
          have h_swap_ok := @pq_swap_ok_hoare
          -- Use validHoare from pq_swap to get nf + postcond.
          -- Work at NondetM level for the seq(dynCom, modify):
          --
          -- The dynCom+call runs the swap body, which only produces ok results (pq_swap_ok_hoare).
          -- After restore: locals = saved.locals, globals = swapped.
          -- After modify(i:=parent): locals.i = parent, everything else = saved.
          -- dataArrayValid preserved: heapUpdate preserves all heapPtrValid
          -- heapPtrValid pq preserved: heapUpdate preserves heapPtrValid
          --
          -- Strategy: resolve call by simp on L1.call + L1ProcEnv.insert,
          -- then use pq_swap_ok_hoare for the resolved body.
          constructor
          · -- non-failure
            intro hf
            -- Outer seq: failed iff dynCom failed or modify after dynCom-ok failed (impossible)
            rw [pq_L1_seq_failed_iff] at hf
            rcases hf with hf_dyn | ⟨s1, hs1_ok, hf_mod⟩
            · -- dynCom failed
              -- L1.dynCom f s = f s s. f s = seq(modify setup)(seq(call "pq_swap")(modify restore))
              -- After modify setup: state = setup s, never fails
              -- Call: resolved to l1_pq_swap_body. At (setup s): need hpv data[i] and data[j=parent].
              --   setup keeps i and sets j=parent. So data[i] valid (hdi) and data[j=parent] valid (hdp).
              -- Modify restore: never fails.
              -- So dynCom doesn't fail.
              show False
              change (L1.dynCom _ s).failed at hf_dyn
              simp only [L1.dynCom] at hf_dyn
              -- Now hf_dyn : (seq(modify setup)(seq(call env "pq_swap")(modify restore)) s).failed
              rw [pq_L1_seq_failed_iff] at hf_dyn
              rcases hf_dyn with hf_setup | ⟨s_setup, hs_setup, hf_rest⟩
              · exact hf_setup -- modify never fails
              · -- After setup: s_setup = setup s. Resolve call.
                rw [pq_L1_seq_failed_iff] at hf_rest
                have hs_eq : s_setup = { s with locals := { s.locals with data := s.locals.data, i := s.locals.i, j := s.locals.parent } } := by
                  have ⟨_, hs⟩ := Prod.mk.inj hs_setup; exact hs
                rcases hf_rest with hf_call | ⟨s_swap, hs_swap, hf_restore⟩
                · -- Call failed. Resolve the call and use pq_swap_ok_hoare.
                  -- After setup: data = s.locals.data, i = s.locals.i, j = s.locals.parent
                  -- pq_swap needs: heapPtrValid data[i] and heapPtrValid data[j]
                  -- At s_setup: i = s.locals.i, j = s.locals.parent, data = s.locals.data
                  -- heapPtrValid data[i] = hdi, heapPtrValid data[j] = hdp
                  -- pq_swap_ok_hoare gives non-failure.
                  -- But we need the call to resolve to l1_pq_swap_body.
                  -- The call uses the incremental env. Resolve by unfolding.
                  rw [hs_eq] at hf_call
                  simp only [L1.call, L1.L1ProcEnv.insert, L1.L1ProcEnv.empty] at hf_call
                  -- Now hf_call should be about l1_pq_swap_body
                  -- Use pq_swap_ok_hoare to show non-failure
                  have h_setup_i : ({ s with locals := { s.locals with data := s.locals.data, i := s.locals.i, j := s.locals.parent } } : ProgramState).locals.i = s.locals.i := rfl
                  have h_setup_j : ({ s with locals := { s.locals with data := s.locals.data, i := s.locals.i, j := s.locals.parent } } : ProgramState).locals.j = s.locals.parent := rfl
                  have h_setup_data : ({ s with locals := { s.locals with data := s.locals.data, i := s.locals.i, j := s.locals.parent } } : ProgramState).locals.data = s.locals.data := rfl
                  have h_setup_globals : ({ s with locals := { s.locals with data := s.locals.data, i := s.locals.i, j := s.locals.parent } } : ProgramState).globals = s.globals := rfl
                  have hdi' : heapPtrValid ({ s with locals := { s.locals with data := s.locals.data, i := s.locals.i, j := s.locals.parent } } : ProgramState).globals.rawHeap
                      (Ptr.elemOffset ({ s with locals := { s.locals with data := s.locals.data, i := s.locals.i, j := s.locals.parent } } : ProgramState).locals.data
                        ({ s with locals := { s.locals with data := s.locals.data, i := s.locals.i, j := s.locals.parent } } : ProgramState).locals.i.toNat) := by
                    rw [h_setup_globals, h_setup_data, h_setup_i]; exact hdi
                  have hdp' : heapPtrValid ({ s with locals := { s.locals with data := s.locals.data, i := s.locals.i, j := s.locals.parent } } : ProgramState).globals.rawHeap
                      (Ptr.elemOffset ({ s with locals := { s.locals with data := s.locals.data, i := s.locals.i, j := s.locals.parent } } : ProgramState).locals.data
                        ({ s with locals := { s.locals with data := s.locals.data, i := s.locals.i, j := s.locals.parent } } : ProgramState).locals.j.toNat) := by
                    rw [h_setup_globals, h_setup_data, h_setup_j]; exact hdp
                  have ⟨h_nf, _⟩ := h_swap_ok _ ⟨hdi', hdp'⟩
                  exact h_nf hf_call
                · exact hf_restore -- modify never fails
            · exact hf_mod -- modify never fails
          · -- postcondition: ok ⇒ I, error ⇒ hpv pq₀
            intro r s' h_mem
            -- Decompose: seq(dynCom, modify(i:=parent))
            change (_ ∨ _) at h_mem
            rcases h_mem with ⟨s_dyn, h_dyn_mem, h_mod_mem⟩ | ⟨h_err_dyn, h_tag⟩
            · -- ok from dynCom, then modify(i:=parent) produces ok
              have ⟨hr_mod, hs_mod⟩ := Prod.mk.inj h_mod_mem
              subst hr_mod; subst hs_mod
              -- s_dyn comes from dynCom: f s s
              change (Except.ok (), s_dyn) ∈ (L1.dynCom _ s).results at h_dyn_mem
              simp only [L1.dynCom] at h_dyn_mem
              -- Decompose: seq(modify setup)(seq(call)(modify restore))
              have ⟨s_setup, h_setup_mem, h_rest⟩ := pq_L1_seq_ok_mem h_dyn_mem
              have h_setup_eq : s_setup = { s with locals := { s.locals with data := s.locals.data, i := s.locals.i, j := s.locals.parent } } := by
                have ⟨_, hs⟩ := Prod.mk.inj h_setup_mem; exact hs
              have ⟨s_call, h_call_mem, h_restore_mem⟩ := pq_L1_seq_ok_mem h_rest
              have h_dyn_eq : s_dyn = { s_call with locals := s.locals } := by
                have ⟨_, hs⟩ := Prod.mk.inj h_restore_mem; exact hs
              -- Resolve the call: simp to get l1_pq_swap_body
              simp only [L1.call, L1.L1ProcEnv.insert, L1.L1ProcEnv.empty] at h_call_mem
              -- h_call_mem should now be about l1_pq_swap_body at s_setup
              -- Use pq_swap_preserves_hpv to get heapPtrValid preservation
              -- Setup state: i = s.i, j = s.parent, data = s.data, globals = s.globals
              have h_setup_globals : s_setup.globals = s.globals := by rw [h_setup_eq]
              have h_setup_i : s_setup.locals.i = s.locals.i := by rw [h_setup_eq]
              have h_setup_j : s_setup.locals.j = s.locals.parent := by rw [h_setup_eq]
              have h_setup_data : s_setup.locals.data = s.locals.data := by rw [h_setup_eq]
              have hdi' : heapPtrValid s_setup.globals.rawHeap (Ptr.elemOffset s_setup.locals.data s_setup.locals.i.toNat) := by
                rw [h_setup_globals, h_setup_data, h_setup_i]; exact hdi
              have hdp' : heapPtrValid s_setup.globals.rawHeap (Ptr.elemOffset s_setup.locals.data s_setup.locals.j.toNat) := by
                rw [h_setup_globals, h_setup_data, h_setup_j]; exact hdp
              have ⟨_, h_hpv_pres⟩ := pq_swap_preserves_hpv s_setup hdi' hdp' _ s_call h_call_mem
              -- Now h_hpv_pres: ∀ p, hpv s_setup.heap p → hpv s_call.heap p
              -- Since s_setup.globals = s.globals: hpv s.heap p → hpv s_call.heap p
              -- s_dyn = { s_call with locals := s.locals }
              -- s' = { s_dyn with locals := { s_dyn.locals with i := s_dyn.locals.parent } }
              -- s'.globals = s_dyn.globals = s_call.globals
              -- s'.locals.i = s_dyn.locals.parent = s.locals.parent
              -- s'.locals.pq = s_dyn.locals.pq = s.locals.pq = pq₀
              -- s'.locals.data = s_dyn.locals.data = s.locals.data
              -- Show I holds (ok case of match):
              simp only [Except.ok.injEq]
              refine ⟨?_, ?_, ?_, ?_⟩
              · -- dataArrayValid: all data[k] for k < n are heapPtrValid
                intro k hk
                have : heapPtrValid s.globals.rawHeap (Ptr.elemOffset s.locals.data k) := hdav k hk
                have := h_hpv_pres UInt32 (Ptr.elemOffset s.locals.data k) (by rw [h_setup_globals]; exact this)
                rw [h_dyn_eq]; exact this
              · -- i.toNat < n: i = parent, parent < n
                rw [h_dyn_eq]; simp only; rw [show ({ s_call with locals := s.locals } : ProgramState).locals.parent = s.locals.parent from rfl]
                exact h_parent_lt
              · -- heapPtrValid pq
                have := h_hpv_pres _ s.locals.pq (by rw [h_setup_globals]; exact hpq)
                rw [h_dyn_eq]; exact this
              · -- pq = pq₀
                rw [h_dyn_eq]; exact hpq_eq
            · -- error from dynCom → error from seq → impossible since modify only produces ok
              -- and dynCom(f s s) only produces ok (swap always ok, modify always ok)
              -- In the L1.seq error branch: (error, s') ∈ (dynCom s).results ∧ r = error
              -- But dynCom only produces ok results (see non-failure proof above).
              -- Actually, the "error" side of L1.seq says:
              -- (Except.error (), s') ∈ (m₁ s).results ∧ r = Except.error ()
              -- So (Except.error (), s') ∈ (dynCom s).results
              -- We need to show this is False.
              -- DynCom = f s s = seq(modify)(seq(call_ok)(modify))
              -- All three produce only ok results.
              -- Actually, the h_tag says r = error
              have h_r_err : r = Except.error () := h_tag
              -- h_err_dyn : (Except.error (), s') ∈ (L1.dynCom _ s).results
              simp only [L1.dynCom] at h_err_dyn
              -- Decompose: (error, s') ∈ seq(modify)(seq(call)(modify)) s
              rcases pq_L1_seq_error_mem h_err_dyn with ⟨s1, h1_ok, h1_err⟩ | h_mod_err
              · -- ok from modify, error from seq(call)(modify)
                rcases pq_L1_seq_error_mem h1_err with ⟨s2, h2_ok, h2_err⟩ | h_call_err
                · -- ok from call, error from modify(restore) — impossible (modify only produces ok)
                  exact absurd h2_err (by intro h; exact absurd (Prod.mk.inj h).1 (by intro h; cases h))
                · -- error from call
                  simp only [L1.call, L1.L1ProcEnv.insert, L1.L1ProcEnv.empty] at h_call_err
                  -- Resolved: call = l1_pq_swap_body
                  -- pq_swap always returns ok (pq_swap_ok_hoare or pq_swap_preserves_hpv)
                  have h_setup_eq' : s1 = { s with locals := { s.locals with data := s.locals.data, i := s.locals.i, j := s.locals.parent } } := by
                    have ⟨_, hs⟩ := Prod.mk.inj (show (Except.ok (), s1) ∈ (L1.modify _ s).results from h1_ok); exact hs
                  have h_setup_globals' : s1.globals = s.globals := by rw [h_setup_eq']
                  have h_setup_i' : s1.locals.i = s.locals.i := by rw [h_setup_eq']
                  have h_setup_j' : s1.locals.j = s.locals.parent := by rw [h_setup_eq']
                  have h_setup_data' : s1.locals.data = s.locals.data := by rw [h_setup_eq']
                  have hdi'' : heapPtrValid s1.globals.rawHeap (Ptr.elemOffset s1.locals.data s1.locals.i.toNat) := by
                    rw [h_setup_globals', h_setup_data', h_setup_i']; exact hdi
                  have hdp'' : heapPtrValid s1.globals.rawHeap (Ptr.elemOffset s1.locals.data s1.locals.j.toNat) := by
                    rw [h_setup_globals', h_setup_data', h_setup_j']; exact hdp
                  have ⟨h_rok, _⟩ := pq_swap_preserves_hpv s1 hdi'' hdp'' _ _ h_call_err
                  exact absurd h_rok (by intro h; cases h)
              · -- error from modify(setup) — impossible (modify only produces ok)
                exact absurd h_mod_err (by intro h; exact absurd (Prod.mk.inj h).1 (by intro h; cases h))
        · -- FALSE branch: throw (error) → error postcond: heapPtrValid pq₀
          intro s ⟨⟨_, _, hpq, hpq_eq, _, _⟩, _⟩
          subst hpq_eq
          exact ⟨not_false, fun r s' h_mem => by
            have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs; exact hpq⟩
    · -- Exit: I ∧ c=false → ok ∧ heapPtrValid pq₀
      intro s ⟨_, _, h_pq, h_eq⟩ _
      subst h_eq; exact ⟨rfl, h_pq⟩
  · -- Handler: skip passes through (R → ok ∧ heapPtrValid pq₀)
    unfold validHoare
    intro s hrs
    refine ⟨not_false, fun r s' h_mem => ?_⟩
    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
    subst hr; subst hs
    exact ⟨rfl, hrs⟩

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
        intro s ⟨hpq, hlt, hdav⟩
        have h_size_lt_cap : (hVal s.globals.rawHeap s.locals.pq).size.toNat <
            (hVal s.globals.rawHeap s.locals.pq).capacity.toNat :=
          UInt32.lt_iff_toNat_lt.mp hlt
        have h_dsize : heapPtrValid s.globals.rawHeap
            (Ptr.elemOffset s.locals.data (hVal s.globals.rawHeap s.locals.pq).size.toNat) :=
          hdav _ h_size_lt_cap
        -- Guard: h_dsize ensures heapPtrValid data[size]
        -- Use L1_guard_modify_result to get singleton ok result
        let p := fun s : ProgramState => heapPtrValid s.globals.rawHeap
            (Ptr.elemOffset s.locals.data (hVal s.globals.rawHeap s.locals.pq).size.toNat)
        let f := fun s : ProgramState =>
          { s with globals := { s.globals with
            rawHeap := heapUpdate s.globals.rawHeap
              (Ptr.elemOffset s.locals.data (hVal s.globals.rawHeap s.locals.pq).size.toNat)
              s.locals.value } }
        have h_gm := L1_guard_modify_result p f s h_dsize
        constructor
        · exact h_gm.2
        · intro r s' h_mem
          rw [h_gm.1] at h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
          -- After heapUpdate: need hpv pq ∧ dav ∧ size < cap
          -- 1. heapPtrValid pq preserved
          have hpq' : heapPtrValid (f s).globals.rawHeap s.locals.pq :=
            heapUpdate_preserves_heapPtrValid _ _ _ _ hpq
          -- 2. dataArrayValid preserved
          have hdav' : dataArrayValid (f s).globals.rawHeap s.locals.data
              (hVal s.globals.rawHeap s.locals.pq).capacity.toNat :=
            dataArrayValid_heapUpdate _ _ _ _ _ hdav
          -- 3. hVal at pq unchanged (UInt32 and C_pqueue have different type tags)
          have h_disj : ptrDisjoint
              (Ptr.elemOffset s.locals.data (hVal s.globals.rawHeap s.locals.pq).size.toNat)
              s.locals.pq :=
            heapPtrValid_different_type_disjoint h_dsize hpq uint32_pqueue_typeTag_ne
          have h_hval_eq : hVal (f s).globals.rawHeap s.locals.pq =
              hVal s.globals.rawHeap s.locals.pq :=
            hVal_heapUpdate_disjoint _ _ _ _ (heapPtrValid_bound h_dsize) (heapPtrValid_bound hpq) h_disj
          rw [h_hval_eq]
          exact ⟨hpq', h_hval_eq ▸ hdav', hlt⟩
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
