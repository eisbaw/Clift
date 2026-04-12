-- Task 0162: Circular DMA buffer verification
--
-- Producer-consumer circular buffer for DMA engines.
-- 10 functions imported from dma_buffer.c (~110 LOC C -> ~480 lines Lean).
--
-- Key verification targets:
-- - Producer-consumer invariant: count <= capacity
-- - Write never overwrites unread data (count < capacity guard)
-- - Read never reads invalid data (count > 0 guard)
-- - Indices stay in [0, capacity)
-- - Write-read roundtrip: write then read returns written value

import Generated.DmaBuffer
import Clift.Lifting.Pipeline
import Clift.Lifting.FuncSpec
import Clift.Specs.RingBuffer

set_option maxHeartbeats 12800000
set_option maxRecDepth 4096

open DmaBuffer

/-! # Step 1: Run the clift pipeline on all 10 functions -/

clift DmaBuffer

/-! # Step 2: Verify L1 definitions exist -/

#check @DmaBuffer.l1_dma_init_body
#check @DmaBuffer.l1_dma_write_body
#check @DmaBuffer.l1_dma_read_body
#check @DmaBuffer.l1_dma_available_body
#check @DmaBuffer.l1_dma_free_space_body
#check @DmaBuffer.l1_dma_is_empty_body
#check @DmaBuffer.l1_dma_is_full_body
#check @DmaBuffer.l1_dma_peek_body
#check @DmaBuffer.l1_dma_reset_body
#check @DmaBuffer.l1_dma_write_batch_body

/-! # Step 3: Producer-consumer invariant -/

/-- DMA buffer invariant:
    1. count <= capacity
    2. write_idx < capacity
    3. read_idx < capacity
    4. indices consistent: write_idx = (read_idx + count) mod capacity -/
def dmaInvariant (write_idx read_idx count capacity : Nat) : Prop :=
  count ≤ capacity ∧
  write_idx < capacity ∧
  read_idx < capacity ∧
  capacity > 0 ∧
  write_idx = (read_idx + count) % capacity

/-- Invariant preserved by write (when count < capacity). -/
theorem dma_write_preserves_inv (w r c cap : Nat)
    (h_inv : dmaInvariant w r c cap)
    (h_not_full : c < cap)
    (h_pow2 : ∃ k, cap = 2^k) :  -- capacity is power of 2
    dmaInvariant ((w + 1) % cap) r (c + 1) cap := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h_inv
  refine ⟨by omega, ?_, h3, h4, ?_⟩
  · exact Nat.mod_lt _ h4
  · -- Goal: (w + 1) % cap = (r + (c + 1)) % cap
    rw [h5, show r + (c + 1) = (r + c) + 1 from by omega]
    -- Goal: ((r + c) % cap + 1) % cap = ((r + c) + 1) % cap
    -- LHS: rewrite using Nat.add_mod then Nat.mod_mod to normalize
    conv => lhs; rw [Nat.add_mod, Nat.mod_mod]
    -- RHS: rewrite using Nat.add_mod
    conv => rhs; rw [Nat.add_mod]

/-- Invariant preserved by read (when count > 0). -/
theorem dma_read_preserves_inv (w r c cap : Nat)
    (h_inv : dmaInvariant w r c cap)
    (h_not_empty : c > 0) :
    dmaInvariant w ((r + 1) % cap) (c - 1) cap := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h_inv
  refine ⟨by omega, h2, Nat.mod_lt _ h4, h4, ?_⟩
  -- Goal: w = ((r + 1) % cap + (c - 1)) % cap
  -- We know w = (r + c) % cap from h5, and c > 0 from h_not_empty
  rw [h5]
  -- Goal: (r + c) % cap = ((r + 1) % cap + (c - 1)) % cap
  -- Key: (r + 1) + (c - 1) = r + c since c > 0
  -- Normalize both sides using Nat.add_mod
  conv => rhs; rw [Nat.add_mod, Nat.mod_mod]
  -- RHS is now ((r + 1) % cap + (c - 1) % cap) % cap
  -- Rewrite LHS: r + c = (r + 1) + (c - 1) since c > 0
  conv => lhs; rw [show r + c = (r + 1) + (c - 1) from by omega]
  rw [Nat.add_mod]

/-- Reset establishes the invariant. -/
theorem dma_reset_establishes_inv (cap : Nat) (h_pos : cap > 0) :
    dmaInvariant 0 0 0 cap := by
  exact ⟨by omega, h_pos, h_pos, h_pos, by simp [Nat.zero_mod]⟩

/-! # Step 4: FuncSpecs -/

/-- dma_init: establishes invariant. -/
def dma_init_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.buf
  post := fun r s =>
    r = Except.ok () →
    let buf := hVal s.globals.rawHeap s.locals.buf
    buf.write_idx = 0 ∧
    buf.read_idx = 0 ∧
    buf.count = 0

/-- dma_write: writes one element. Returns 0 on success, 1 if full.
    Precondition requires validity of buf and the data[write_idx] element. -/
def dma_write_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.buf ∧
    heapPtrValid s.globals.rawHeap
      (Ptr.elemOffset s.locals.data (hVal s.globals.rawHeap s.locals.buf).write_idx.toNat) ∧
    (hVal s.globals.rawHeap s.locals.buf).count <
      (hVal s.globals.rawHeap s.locals.buf).capacity
  post := fun r s =>
    r = Except.ok () →
    s.locals.ret__val = 0

/-- dma_read: reads one element. Returns 0 on success, 1 if empty.
    Precondition requires validity of buf, out, and data[read_idx]. -/
def dma_read_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.buf ∧
    heapPtrValid s.globals.rawHeap s.locals.out ∧
    heapPtrValid s.globals.rawHeap
      (Ptr.elemOffset s.locals.data (hVal s.globals.rawHeap s.locals.buf).read_idx.toNat) ∧
    (hVal s.globals.rawHeap s.locals.buf).count > 0
  post := fun r s =>
    r = Except.ok () →
    s.locals.ret__val = 0

/-- dma_available: returns count. -/
def dma_available_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.buf
  post := fun r s =>
    r = Except.ok () →
    s.locals.ret__val = (hVal s.globals.rawHeap s.locals.buf).count

/-- dma_is_empty: checks count == 0. -/
def dma_is_empty_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.buf
  post := fun r s =>
    r = Except.ok () →
    let buf := hVal s.globals.rawHeap s.locals.buf
    (buf.count = 0 → s.locals.ret__val = 1) ∧
    (buf.count ≠ 0 → s.locals.ret__val = 0)

/-- dma_is_full: checks count >= capacity. -/
def dma_is_full_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.buf
  post := fun r s =>
    r = Except.ok () →
    let buf := hVal s.globals.rawHeap s.locals.buf
    (buf.count >= buf.capacity → s.locals.ret__val = 1) ∧
    (buf.count < buf.capacity → s.locals.ret__val = 0)

/-! # Step 5: validHoare theorems -/

-- Helper: heapUpdate preserves heapPtrValid at same pointer for C_dma_buffer
private theorem dma_heapUpdate_buf_ptrValid (s : ProgramState)
    (hv : heapPtrValid s.globals.rawHeap s.locals.buf)
    (v : DmaBuffer.C_dma_buffer) :
    heapPtrValid (heapUpdate s.globals.rawHeap s.locals.buf v) s.locals.buf :=
  heapUpdate_preserves_heapPtrValid _ _ _ _ hv

theorem dma_init_correct :
    dma_init_spec.satisfiedBy DmaBuffer.l1_dma_init_body := by
  unfold FuncSpec.satisfiedBy dma_init_spec validHoare
  intro s hpre
  -- L1 body: catch (seq (seq guard modify) (seq (seq guard modify) (seq (seq guard modify) (seq guard modify)))) skip
  let p := fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.buf
  let f1 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.buf ({ hVal s.globals.rawHeap s.locals.buf with write_idx := 0 } : DmaBuffer.C_dma_buffer) } }
  let f2 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.buf ({ hVal s.globals.rawHeap s.locals.buf with read_idx := 0 } : DmaBuffer.C_dma_buffer) } }
  let f3 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.buf ({ hVal s.globals.rawHeap s.locals.buf with count := 0 } : DmaBuffer.C_dma_buffer) } }
  let f4 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.buf ({ hVal s.globals.rawHeap s.locals.buf with capacity := s.locals.capacity } : DmaBuffer.C_dma_buffer) } }
  let s1 := f1 s
  let s2 := f2 s1
  let s3 := f3 s2
  let s4 := f4 s3
  -- heapPtrValid preservation
  have hv1 : p s1 := dma_heapUpdate_buf_ptrValid s hpre _
  have hv2 : p s2 := dma_heapUpdate_buf_ptrValid s1 hv1 _
  have hv3 : p s3 := dma_heapUpdate_buf_ptrValid s2 hv2 _
  -- Step results
  have h1 := L1_guard_modify_result p f1 s hpre
  have h2 := L1_guard_modify_result p f2 s1 hv1
  have h3 := L1_guard_modify_result p f3 s2 hv2
  have h4 := L1_guard_modify_result p f4 s3 hv3
  -- Chain steps 3,4
  have h34 := L1_seq_singleton_ok h3.1 h3.2 (m₂ := L1.seq (L1.guard p) (L1.modify f4))
  have h34_res : (L1.seq (L1.seq (L1.guard p) (L1.modify f3)) (L1.seq (L1.guard p) (L1.modify f4)) s2).results = {(Except.ok (), s4)} := by
    rw [h34.1, h4.1]
  have h34_nf : ¬(L1.seq (L1.seq (L1.guard p) (L1.modify f3)) (L1.seq (L1.guard p) (L1.modify f4)) s2).failed :=
    fun hf => h4.2 (h34.2.mp hf)
  -- Chain steps 2,3,4
  have h234 := L1_seq_singleton_ok h2.1 h2.2
    (m₂ := L1.seq (L1.seq (L1.guard p) (L1.modify f3)) (L1.seq (L1.guard p) (L1.modify f4)))
  have h234_res : (L1.seq (L1.seq (L1.guard p) (L1.modify f2)) (L1.seq (L1.seq (L1.guard p) (L1.modify f3)) (L1.seq (L1.guard p) (L1.modify f4))) s1).results = {(Except.ok (), s4)} := by
    rw [h234.1, h34_res]
  have h234_nf : ¬(L1.seq (L1.seq (L1.guard p) (L1.modify f2)) (L1.seq (L1.seq (L1.guard p) (L1.modify f3)) (L1.seq (L1.guard p) (L1.modify f4))) s1).failed :=
    fun hf => h34_nf (h234.2.mp hf)
  -- Chain all 4 steps
  have h1234 := L1_seq_singleton_ok h1.1 h1.2
    (m₂ := L1.seq (L1.seq (L1.guard p) (L1.modify f2)) (L1.seq (L1.seq (L1.guard p) (L1.modify f3)) (L1.seq (L1.guard p) (L1.modify f4))))
  have h1234_res : (L1.seq (L1.seq (L1.guard p) (L1.modify f1)) (L1.seq (L1.seq (L1.guard p) (L1.modify f2)) (L1.seq (L1.seq (L1.guard p) (L1.modify f3)) (L1.seq (L1.guard p) (L1.modify f4)))) s).results = {(Except.ok (), s4)} := by
    rw [h1234.1, h234_res]
  have h1234_nf : ¬(L1.seq (L1.seq (L1.guard p) (L1.modify f1)) (L1.seq (L1.seq (L1.guard p) (L1.modify f2)) (L1.seq (L1.seq (L1.guard p) (L1.modify f3)) (L1.seq (L1.guard p) (L1.modify f4)))) s).failed :=
    fun hf => h234_nf (h1234.2.mp hf)
  -- Catch wrapper
  have h_catch := L1_catch_singleton_ok h1234_res h1234_nf
  unfold DmaBuffer.l1_dma_init_body
  constructor
  · exact h_catch.2
  · intro r s' h_mem
    rw [h_catch.1] at h_mem
    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
    subst hr; subst hs
    intro _
    -- Postcondition: hVal at s4 has write_idx=0, read_idx=0, count=0
    have hb := heapPtrValid_bound hpre
    have hb1 := heapPtrValid_bound hv1
    have hb2 := heapPtrValid_bound hv2
    have hb3 := heapPtrValid_bound hv3
    have h4v : hVal s4.globals.rawHeap s4.locals.buf =
        ({ hVal s3.globals.rawHeap s3.locals.buf with capacity := s.locals.capacity } : DmaBuffer.C_dma_buffer) :=
      hVal_heapUpdate_same _ _ _ hb3
    have h3v : hVal s3.globals.rawHeap s3.locals.buf =
        ({ hVal s2.globals.rawHeap s2.locals.buf with count := 0 } : DmaBuffer.C_dma_buffer) :=
      hVal_heapUpdate_same _ _ _ hb2
    have h2v : hVal s2.globals.rawHeap s2.locals.buf =
        ({ hVal s1.globals.rawHeap s1.locals.buf with read_idx := 0 } : DmaBuffer.C_dma_buffer) :=
      hVal_heapUpdate_same _ _ _ hb1
    have h1v : hVal s1.globals.rawHeap s1.locals.buf =
        ({ hVal s.globals.rawHeap s.locals.buf with write_idx := 0 } : DmaBuffer.C_dma_buffer) :=
      hVal_heapUpdate_same _ _ _ hb
    rw [h4v, h3v, h2v, h1v]
    exact ⟨rfl, rfl, rfl⟩

private theorem dma_retval_globals (s : ProgramState) (v : UInt32) :
    ({ s with locals := { s.locals with ret__val := v } } : ProgramState).globals = s.globals := rfl
private theorem dma_retval_buf (s : ProgramState) (v : UInt32) :
    ({ s with locals := { s.locals with ret__val := v } } : ProgramState).locals.buf = s.locals.buf := rfl
private theorem dma_retval_val (s : ProgramState) (v : UInt32) :
    ({ s with locals := { s.locals with ret__val := v } } : ProgramState).locals.ret__val = v := rfl

attribute [local irreducible] hVal heapPtrValid in
theorem dma_available_correct :
    dma_available_spec.satisfiedBy DmaBuffer.l1_dma_available_body := by
  unfold FuncSpec.satisfiedBy dma_available_spec validHoare
  intro s hpre
  unfold DmaBuffer.l1_dma_available_body
  have h := L1_guard_modify_throw_catch_skip_result
    (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.buf)
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := (hVal s.globals.rawHeap s.locals.buf).count } })
    s hpre
  obtain ⟨h_res, h_nf⟩ := h
  constructor
  · exact h_nf
  · intro r s' h_mem _
    rw [h_res] at h_mem
    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
    subst hr; subst hs
    rw [dma_retval_val, dma_retval_globals, dma_retval_buf]

/-! ## Helper: L1.condition elimination -/

private theorem L1_elim_cond_false {S : Type}
    (c : S → Bool) {t e m handler : L1Monad S} {s : S} (h : c s = false) :
    L1.catch (L1.seq (L1.condition c t e) m) handler s =
    L1.catch (L1.seq e m) handler s := by
  unfold L1.catch L1.seq L1.condition; simp [h]

/-! ## Step functions with anonymous constructors (avoiding kernel deep recursion)

  Locals fields in order: buf, cap_mask, capacity, data, n, out, ret__val, value, values, written
  CState fields: globals, locals
  Globals fields: rawHeap -/

/-- Set cap_mask := (hVal buf).capacity - 1 (locals-only update). -/
private noncomputable def dma_set_cap_mask (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.buf, (hVal s.globals.rawHeap s.locals.buf).capacity - 1,
    s.locals.capacity, s.locals.data, s.locals.n, s.locals.out,
    s.locals.ret__val, s.locals.value, s.locals.values, s.locals.written⟩⟩

/-- Set ret__val := 0 (locals-only update). -/
private noncomputable def dma_set_ret0 (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.buf, s.locals.cap_mask, s.locals.capacity, s.locals.data,
    s.locals.n, s.locals.out, 0, s.locals.value, s.locals.values, s.locals.written⟩⟩

/-- Write value to data[write_idx] (heap-only update). -/
private noncomputable def dw_heap_data (s : ProgramState) : ProgramState :=
  ⟨⟨heapUpdate s.globals.rawHeap
    (Ptr.elemOffset s.locals.data (hVal s.globals.rawHeap s.locals.buf).write_idx.toNat)
    s.locals.value⟩, s.locals⟩

/-- Update buf.write_idx := (write_idx + 1) &&& cap_mask (heap-only update). -/
private noncomputable def dw_heap_write_idx (s : ProgramState) : ProgramState :=
  ⟨⟨heapUpdate s.globals.rawHeap s.locals.buf
    ({ hVal s.globals.rawHeap s.locals.buf with
       write_idx := ((hVal s.globals.rawHeap s.locals.buf).write_idx + 1) &&& s.locals.cap_mask })⟩,
   s.locals⟩

/-- Update buf.count := count + 1 (heap-only update). -/
private noncomputable def dw_heap_count (s : ProgramState) : ProgramState :=
  ⟨⟨heapUpdate s.globals.rawHeap s.locals.buf
    ({ hVal s.globals.rawHeap s.locals.buf with
       count := (hVal s.globals.rawHeap s.locals.buf).count + 1 })⟩,
   s.locals⟩

/-- Write hVal(data[read_idx]) to out ptr (heap-only update). -/
private noncomputable def dr_heap_out (s : ProgramState) : ProgramState :=
  ⟨⟨heapUpdate s.globals.rawHeap s.locals.out
    (hVal s.globals.rawHeap
      (Ptr.elemOffset s.locals.data (hVal s.globals.rawHeap s.locals.buf).read_idx.toNat))⟩,
   s.locals⟩

/-- Update buf.read_idx := (read_idx + 1) &&& cap_mask (heap-only update). -/
private noncomputable def dr_heap_read_idx (s : ProgramState) : ProgramState :=
  ⟨⟨heapUpdate s.globals.rawHeap s.locals.buf
    ({ hVal s.globals.rawHeap s.locals.buf with
       read_idx := ((hVal s.globals.rawHeap s.locals.buf).read_idx + 1) &&& s.locals.cap_mask })⟩,
   s.locals⟩

/-- Update buf.count := count - 1 (heap-only update). -/
private noncomputable def dr_heap_count (s : ProgramState) : ProgramState :=
  ⟨⟨heapUpdate s.globals.rawHeap s.locals.buf
    ({ hVal s.globals.rawHeap s.locals.buf with
       count := (hVal s.globals.rawHeap s.locals.buf).count - 1 })⟩,
   s.locals⟩

/-! ### Projection lemmas for dma_set_cap_mask -/

attribute [local irreducible] hVal in
private theorem dma_set_cap_mask_locals_eq (s : ProgramState) :
    (dma_set_cap_mask s).locals =
      ⟨s.locals.buf, (hVal s.globals.rawHeap s.locals.buf).capacity - 1,
       s.locals.capacity, s.locals.data, s.locals.n, s.locals.out,
       s.locals.ret__val, s.locals.value, s.locals.values, s.locals.written⟩ := by
  show (⟨s.globals, ⟨s.locals.buf, (hVal s.globals.rawHeap s.locals.buf).capacity - 1,
    s.locals.capacity, s.locals.data, s.locals.n, s.locals.out,
    s.locals.ret__val, s.locals.value, s.locals.values, s.locals.written⟩⟩ :
    ProgramState).locals = _; rfl

attribute [local irreducible] hVal in
@[simp] private theorem dma_set_cap_mask_globals (s : ProgramState) :
    (dma_set_cap_mask s).globals = s.globals := by
  show (⟨s.globals, ⟨s.locals.buf, (hVal s.globals.rawHeap s.locals.buf).capacity - 1,
    s.locals.capacity, s.locals.data, s.locals.n, s.locals.out,
    s.locals.ret__val, s.locals.value, s.locals.values, s.locals.written⟩⟩ :
    ProgramState).globals = _; rfl

@[simp] private theorem dma_set_cap_mask_buf (s : ProgramState) :
    (dma_set_cap_mask s).locals.buf = s.locals.buf := by rw [dma_set_cap_mask_locals_eq]
@[simp] private theorem dma_set_cap_mask_data (s : ProgramState) :
    (dma_set_cap_mask s).locals.data = s.locals.data := by rw [dma_set_cap_mask_locals_eq]
@[simp] private theorem dma_set_cap_mask_out (s : ProgramState) :
    (dma_set_cap_mask s).locals.out = s.locals.out := by rw [dma_set_cap_mask_locals_eq]
@[simp] private theorem dma_set_cap_mask_value (s : ProgramState) :
    (dma_set_cap_mask s).locals.value = s.locals.value := by rw [dma_set_cap_mask_locals_eq]
attribute [local irreducible] hVal in
@[simp] private theorem dma_set_cap_mask_cap_mask (s : ProgramState) :
    (dma_set_cap_mask s).locals.cap_mask =
      (hVal s.globals.rawHeap s.locals.buf).capacity - 1 := by rw [dma_set_cap_mask_locals_eq]
@[simp] private theorem dma_set_cap_mask_ret__val (s : ProgramState) :
    (dma_set_cap_mask s).locals.ret__val = s.locals.ret__val := by rw [dma_set_cap_mask_locals_eq]

/-! ### Projection lemmas for dma_set_ret0 -/

@[simp] private theorem dma_set_ret0_globals (s : ProgramState) :
    (dma_set_ret0 s).globals = s.globals := by
  show (⟨s.globals, ⟨s.locals.buf, s.locals.cap_mask, s.locals.capacity, s.locals.data,
    s.locals.n, s.locals.out, 0, s.locals.value, s.locals.values, s.locals.written⟩⟩ :
    ProgramState).globals = _; rfl

private theorem dma_set_ret0_locals_eq (s : ProgramState) :
    (dma_set_ret0 s).locals =
      ⟨s.locals.buf, s.locals.cap_mask, s.locals.capacity, s.locals.data,
       s.locals.n, s.locals.out, 0, s.locals.value, s.locals.values, s.locals.written⟩ := by
  show (⟨s.globals, ⟨s.locals.buf, s.locals.cap_mask, s.locals.capacity, s.locals.data,
    s.locals.n, s.locals.out, 0, s.locals.value, s.locals.values, s.locals.written⟩⟩ :
    ProgramState).locals = _; rfl

@[simp] private theorem dma_set_ret0_buf (s : ProgramState) :
    (dma_set_ret0 s).locals.buf = s.locals.buf := by rw [dma_set_ret0_locals_eq]
@[simp] private theorem dma_set_ret0_ret__val (s : ProgramState) :
    (dma_set_ret0 s).locals.ret__val = 0 := by rw [dma_set_ret0_locals_eq]

/-! ### Projection lemmas for heap-update step functions -/

-- dw_heap_data: ⟨⟨heapUpdate ...⟩, s.locals⟩
attribute [local irreducible] hVal heapUpdate in
@[simp] private theorem dw_heap_data_locals (s : ProgramState) :
    (dw_heap_data s).locals = s.locals := by
  show (⟨⟨heapUpdate s.globals.rawHeap
    (Ptr.elemOffset s.locals.data (hVal s.globals.rawHeap s.locals.buf).write_idx.toNat)
    s.locals.value⟩, s.locals⟩ : ProgramState).locals = _; rfl

attribute [local irreducible] hVal heapUpdate in
private theorem dw_heap_data_globals_eq (s : ProgramState) :
    (dw_heap_data s).globals =
      ⟨heapUpdate s.globals.rawHeap
        (Ptr.elemOffset s.locals.data (hVal s.globals.rawHeap s.locals.buf).write_idx.toNat)
        s.locals.value⟩ := by
  show (⟨⟨heapUpdate s.globals.rawHeap
    (Ptr.elemOffset s.locals.data (hVal s.globals.rawHeap s.locals.buf).write_idx.toNat)
    s.locals.value⟩, s.locals⟩ : ProgramState).globals = _; rfl

attribute [local irreducible] hVal heapUpdate in
@[simp] private theorem dw_heap_data_rawHeap (s : ProgramState) :
    (dw_heap_data s).globals.rawHeap =
      heapUpdate s.globals.rawHeap
        (Ptr.elemOffset s.locals.data (hVal s.globals.rawHeap s.locals.buf).write_idx.toNat)
        s.locals.value := by rw [dw_heap_data_globals_eq]

-- dw_heap_write_idx: ⟨⟨heapUpdate ... buf ...⟩, s.locals⟩
attribute [local irreducible] hVal heapUpdate in
@[simp] private theorem dw_heap_write_idx_locals (s : ProgramState) :
    (dw_heap_write_idx s).locals = s.locals := by
  show (⟨⟨heapUpdate s.globals.rawHeap s.locals.buf
    ({ hVal s.globals.rawHeap s.locals.buf with
       write_idx := ((hVal s.globals.rawHeap s.locals.buf).write_idx + 1) &&& s.locals.cap_mask })⟩,
    s.locals⟩ : ProgramState).locals = _; rfl

attribute [local irreducible] hVal heapUpdate in
private theorem dw_heap_write_idx_globals_eq (s : ProgramState) :
    (dw_heap_write_idx s).globals =
      ⟨heapUpdate s.globals.rawHeap s.locals.buf
        ({ hVal s.globals.rawHeap s.locals.buf with
           write_idx := ((hVal s.globals.rawHeap s.locals.buf).write_idx + 1) &&& s.locals.cap_mask })⟩ := by
  show (⟨⟨heapUpdate s.globals.rawHeap s.locals.buf
    ({ hVal s.globals.rawHeap s.locals.buf with
       write_idx := ((hVal s.globals.rawHeap s.locals.buf).write_idx + 1) &&& s.locals.cap_mask })⟩,
    s.locals⟩ : ProgramState).globals = _; rfl

attribute [local irreducible] hVal heapUpdate in
@[simp] private theorem dw_heap_write_idx_rawHeap (s : ProgramState) :
    (dw_heap_write_idx s).globals.rawHeap =
      heapUpdate s.globals.rawHeap s.locals.buf
        ({ hVal s.globals.rawHeap s.locals.buf with
           write_idx := ((hVal s.globals.rawHeap s.locals.buf).write_idx + 1) &&& s.locals.cap_mask }) := by
  rw [dw_heap_write_idx_globals_eq]

-- dw_heap_count: ⟨⟨heapUpdate ... buf ...⟩, s.locals⟩
attribute [local irreducible] hVal heapUpdate in
@[simp] private theorem dw_heap_count_locals (s : ProgramState) :
    (dw_heap_count s).locals = s.locals := by
  show (⟨⟨heapUpdate s.globals.rawHeap s.locals.buf
    ({ hVal s.globals.rawHeap s.locals.buf with
       count := (hVal s.globals.rawHeap s.locals.buf).count + 1 })⟩,
    s.locals⟩ : ProgramState).locals = _; rfl

attribute [local irreducible] hVal heapUpdate in
private theorem dw_heap_count_globals_eq (s : ProgramState) :
    (dw_heap_count s).globals =
      ⟨heapUpdate s.globals.rawHeap s.locals.buf
        ({ hVal s.globals.rawHeap s.locals.buf with
           count := (hVal s.globals.rawHeap s.locals.buf).count + 1 })⟩ := by
  show (⟨⟨heapUpdate s.globals.rawHeap s.locals.buf
    ({ hVal s.globals.rawHeap s.locals.buf with
       count := (hVal s.globals.rawHeap s.locals.buf).count + 1 })⟩,
    s.locals⟩ : ProgramState).globals = _; rfl

attribute [local irreducible] hVal heapUpdate in
@[simp] private theorem dw_heap_count_rawHeap (s : ProgramState) :
    (dw_heap_count s).globals.rawHeap =
      heapUpdate s.globals.rawHeap s.locals.buf
        ({ hVal s.globals.rawHeap s.locals.buf with
           count := (hVal s.globals.rawHeap s.locals.buf).count + 1 }) := by
  rw [dw_heap_count_globals_eq]

-- dr_heap_out: ⟨⟨heapUpdate ... out ...⟩, s.locals⟩
attribute [local irreducible] hVal heapUpdate in
@[simp] private theorem dr_heap_out_locals (s : ProgramState) :
    (dr_heap_out s).locals = s.locals := by
  show (⟨⟨heapUpdate s.globals.rawHeap s.locals.out
    (hVal s.globals.rawHeap
      (Ptr.elemOffset s.locals.data (hVal s.globals.rawHeap s.locals.buf).read_idx.toNat))⟩,
    s.locals⟩ : ProgramState).locals = _; rfl

attribute [local irreducible] hVal heapUpdate in
private theorem dr_heap_out_globals_eq (s : ProgramState) :
    (dr_heap_out s).globals =
      ⟨heapUpdate s.globals.rawHeap s.locals.out
        (hVal s.globals.rawHeap
          (Ptr.elemOffset s.locals.data (hVal s.globals.rawHeap s.locals.buf).read_idx.toNat))⟩ := by
  show (⟨⟨heapUpdate s.globals.rawHeap s.locals.out
    (hVal s.globals.rawHeap
      (Ptr.elemOffset s.locals.data (hVal s.globals.rawHeap s.locals.buf).read_idx.toNat))⟩,
    s.locals⟩ : ProgramState).globals = _; rfl

attribute [local irreducible] hVal heapUpdate in
@[simp] private theorem dr_heap_out_rawHeap (s : ProgramState) :
    (dr_heap_out s).globals.rawHeap =
      heapUpdate s.globals.rawHeap s.locals.out
        (hVal s.globals.rawHeap
          (Ptr.elemOffset s.locals.data (hVal s.globals.rawHeap s.locals.buf).read_idx.toNat)) := by
  rw [dr_heap_out_globals_eq]

-- dr_heap_read_idx: ⟨⟨heapUpdate ... buf ...⟩, s.locals⟩
attribute [local irreducible] hVal heapUpdate in
@[simp] private theorem dr_heap_read_idx_locals (s : ProgramState) :
    (dr_heap_read_idx s).locals = s.locals := by
  show (⟨⟨heapUpdate s.globals.rawHeap s.locals.buf
    ({ hVal s.globals.rawHeap s.locals.buf with
       read_idx := ((hVal s.globals.rawHeap s.locals.buf).read_idx + 1) &&& s.locals.cap_mask })⟩,
    s.locals⟩ : ProgramState).locals = _; rfl

attribute [local irreducible] hVal heapUpdate in
private theorem dr_heap_read_idx_globals_eq (s : ProgramState) :
    (dr_heap_read_idx s).globals =
      ⟨heapUpdate s.globals.rawHeap s.locals.buf
        ({ hVal s.globals.rawHeap s.locals.buf with
           read_idx := ((hVal s.globals.rawHeap s.locals.buf).read_idx + 1) &&& s.locals.cap_mask })⟩ := by
  show (⟨⟨heapUpdate s.globals.rawHeap s.locals.buf
    ({ hVal s.globals.rawHeap s.locals.buf with
       read_idx := ((hVal s.globals.rawHeap s.locals.buf).read_idx + 1) &&& s.locals.cap_mask })⟩,
    s.locals⟩ : ProgramState).globals = _; rfl

attribute [local irreducible] hVal heapUpdate in
@[simp] private theorem dr_heap_read_idx_rawHeap (s : ProgramState) :
    (dr_heap_read_idx s).globals.rawHeap =
      heapUpdate s.globals.rawHeap s.locals.buf
        ({ hVal s.globals.rawHeap s.locals.buf with
           read_idx := ((hVal s.globals.rawHeap s.locals.buf).read_idx + 1) &&& s.locals.cap_mask }) := by
  rw [dr_heap_read_idx_globals_eq]

-- dr_heap_count: ⟨⟨heapUpdate ... buf ...⟩, s.locals⟩
attribute [local irreducible] hVal heapUpdate in
@[simp] private theorem dr_heap_count_locals (s : ProgramState) :
    (dr_heap_count s).locals = s.locals := by
  show (⟨⟨heapUpdate s.globals.rawHeap s.locals.buf
    ({ hVal s.globals.rawHeap s.locals.buf with
       count := (hVal s.globals.rawHeap s.locals.buf).count - 1 })⟩,
    s.locals⟩ : ProgramState).locals = _; rfl

attribute [local irreducible] hVal heapUpdate in
private theorem dr_heap_count_globals_eq (s : ProgramState) :
    (dr_heap_count s).globals =
      ⟨heapUpdate s.globals.rawHeap s.locals.buf
        ({ hVal s.globals.rawHeap s.locals.buf with
           count := (hVal s.globals.rawHeap s.locals.buf).count - 1 })⟩ := by
  show (⟨⟨heapUpdate s.globals.rawHeap s.locals.buf
    ({ hVal s.globals.rawHeap s.locals.buf with
       count := (hVal s.globals.rawHeap s.locals.buf).count - 1 })⟩,
    s.locals⟩ : ProgramState).globals = _; rfl

attribute [local irreducible] hVal heapUpdate in
@[simp] private theorem dr_heap_count_rawHeap (s : ProgramState) :
    (dr_heap_count s).globals.rawHeap =
      heapUpdate s.globals.rawHeap s.locals.buf
        ({ hVal s.globals.rawHeap s.locals.buf with
           count := (hVal s.globals.rawHeap s.locals.buf).count - 1 }) := by
  rw [dr_heap_count_globals_eq]

/-! ### heapPtrValid preservation through step functions -/

private theorem dma_set_cap_mask_ptrValid_buf (s : ProgramState)
    (h : heapPtrValid s.globals.rawHeap s.locals.buf) :
    heapPtrValid (dma_set_cap_mask s).globals.rawHeap (dma_set_cap_mask s).locals.buf := by
  simp only [dma_set_cap_mask_globals, dma_set_cap_mask_buf]; exact h

private theorem dma_set_cap_mask_ptrValid_data (s : ProgramState)
    (h : heapPtrValid s.globals.rawHeap
      (Ptr.elemOffset s.locals.data (hVal s.globals.rawHeap s.locals.buf).write_idx.toNat)) :
    heapPtrValid (dma_set_cap_mask s).globals.rawHeap
      (Ptr.elemOffset (dma_set_cap_mask s).locals.data
        (hVal (dma_set_cap_mask s).globals.rawHeap (dma_set_cap_mask s).locals.buf).write_idx.toNat) := by
  simp only [dma_set_cap_mask_globals, dma_set_cap_mask_data, dma_set_cap_mask_buf]; exact h

private theorem dw_heap_data_ptrValid_buf (s : ProgramState)
    (h : heapPtrValid s.globals.rawHeap s.locals.buf) :
    heapPtrValid (dw_heap_data s).globals.rawHeap (dw_heap_data s).locals.buf := by
  simp only [dw_heap_data_rawHeap, dw_heap_data_locals]
  exact heapUpdate_preserves_heapPtrValid _ _ _ _ h

private theorem dw_heap_write_idx_ptrValid_buf (s : ProgramState)
    (h : heapPtrValid s.globals.rawHeap s.locals.buf) :
    heapPtrValid (dw_heap_write_idx s).globals.rawHeap (dw_heap_write_idx s).locals.buf := by
  simp only [dw_heap_write_idx_rawHeap, dw_heap_write_idx_locals]
  exact heapUpdate_preserves_heapPtrValid _ _ _ _ h

private theorem dw_heap_count_ptrValid_buf (s : ProgramState)
    (h : heapPtrValid s.globals.rawHeap s.locals.buf) :
    heapPtrValid (dw_heap_count s).globals.rawHeap (dw_heap_count s).locals.buf := by
  simp only [dw_heap_count_rawHeap, dw_heap_count_locals]
  exact heapUpdate_preserves_heapPtrValid _ _ _ _ h

/-! ### Manual L1 bodies using anonymous-constructor step functions

  The clift-generated L1 bodies use `{ s with ... }` which causes kernel deep recursion
  on the 10-field Locals struct. We define equivalent L1 bodies using named step functions
  with anonymous constructors, prove they're equal, then prove validHoare on the manual bodies. -/

private noncomputable def l1_dma_write_manual : L1Monad ProgramState :=
  let p := fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.buf
  let pd := fun s : ProgramState => heapPtrValid s.globals.rawHeap
    (Ptr.elemOffset s.locals.data (hVal s.globals.rawHeap s.locals.buf).write_idx.toNat)
  L1.catch
    (L1.seq (L1.condition
      (fun s => decide ((hVal s.globals.rawHeap s.locals.buf).count >=
        (hVal s.globals.rawHeap s.locals.buf).capacity))
      (L1.seq (L1.modify (fun s : ProgramState =>
        ⟨s.globals, ⟨s.locals.buf, s.locals.cap_mask, s.locals.capacity, s.locals.data,
          s.locals.n, s.locals.out, 1, s.locals.value, s.locals.values, s.locals.written⟩⟩))
        L1.throw) L1.skip)
    (L1.seq (L1.seq (L1.guard p) (L1.modify dma_set_cap_mask))
      (L1.seq (L1.seq (L1.guard pd) (L1.modify dw_heap_data))
        (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify dw_heap_write_idx)))
          (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify dw_heap_count)))
            (L1.seq (L1.modify dma_set_ret0) L1.throw))))))
    L1.skip

private noncomputable def l1_dma_read_manual : L1Monad ProgramState :=
  let p := fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.buf
  let po := fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.out
  let prd := fun s : ProgramState => heapPtrValid s.globals.rawHeap
    (Ptr.elemOffset s.locals.data (hVal s.globals.rawHeap s.locals.buf).read_idx.toNat)
  L1.catch
    (L1.seq (L1.condition
      (fun s => decide ((hVal s.globals.rawHeap s.locals.buf).count = 0))
      (L1.seq (L1.modify (fun s : ProgramState =>
        ⟨s.globals, ⟨s.locals.buf, s.locals.cap_mask, s.locals.capacity, s.locals.data,
          s.locals.n, s.locals.out, 1, s.locals.value, s.locals.values, s.locals.written⟩⟩))
        L1.throw) L1.skip)
    (L1.seq (L1.seq (L1.guard p) (L1.modify dma_set_cap_mask))
      (L1.seq (L1.seq (L1.guard po) (L1.seq (L1.guard prd) (L1.seq (L1.guard p) (L1.modify dr_heap_out))))
        (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify dr_heap_read_idx)))
          (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify dr_heap_count)))
            (L1.seq (L1.modify dma_set_ret0) L1.throw))))))
    L1.skip

/-! ### dma_write proof -/

theorem dma_write_correct :
    dma_write_spec.satisfiedBy DmaBuffer.l1_dma_write_body := by
  -- The manual body is definitionally equal to the generated one
  suffices h : dma_write_spec.satisfiedBy l1_dma_write_manual from h
  unfold FuncSpec.satisfiedBy dma_write_spec validHoare
  intro s ⟨hbuf, hdata, hlt⟩
  have hcond : decide ((hVal s.globals.rawHeap s.locals.buf).count >=
      (hVal s.globals.rawHeap s.locals.buf).capacity) = false := by
    rw [decide_eq_false_iff_not]; intro h
    exact absurd (UInt32.le_iff_toNat_le.mp h) (Nat.not_le.mpr (UInt32.lt_iff_toNat_lt.mp hlt))
  unfold l1_dma_write_manual
  rw [L1_elim_cond_false
    (fun st : ProgramState => decide ((hVal st.globals.rawHeap st.locals.buf).count >=
      (hVal st.globals.rawHeap st.locals.buf).capacity)) hcond]
  -- After cond false: catch (seq skip rest) skip
  let p := fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.buf
  let pd := fun s : ProgramState => heapPtrValid s.globals.rawHeap
    (Ptr.elemOffset s.locals.data (hVal s.globals.rawHeap s.locals.buf).write_idx.toNat)
  -- Intermediate states
  let s1 := dma_set_cap_mask s
  let s2 := dw_heap_data s1
  let s3 := dw_heap_write_idx s2
  let s4 := dw_heap_count s3
  let s5 := dma_set_ret0 s4
  -- heapPtrValid preservation
  have hbuf1 : p s1 := dma_set_cap_mask_ptrValid_buf s hbuf
  have hdata1 : pd s1 := dma_set_cap_mask_ptrValid_data s hdata
  have hbuf2 : p s2 := dw_heap_data_ptrValid_buf s1 hbuf1
  have hbuf3 : p s3 := dw_heap_write_idx_ptrValid_buf s2 hbuf2
  -- Step results
  have h1 := L1_guard_modify_result p dma_set_cap_mask s hbuf
  have h2 := L1_guard_modify_result pd dw_heap_data s1 hdata1
  have h3 := L1_guard_guard_modify_result p p dw_heap_write_idx s2 hbuf2 hbuf2
  have h4 := L1_guard_guard_modify_result p p dw_heap_count s3 hbuf3 hbuf3
  have h5 := L1_modify_throw_result dma_set_ret0 s4
  -- Define monad terms (matching the manual body structure)
  let m5 : L1Monad ProgramState := L1.seq (L1.modify dma_set_ret0) L1.throw
  let m4 : L1Monad ProgramState := L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify dw_heap_count))) m5
  let m3 : L1Monad ProgramState := L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify dw_heap_write_idx))) m4
  let m2 : L1Monad ProgramState := L1.seq (L1.seq (L1.guard pd) (L1.modify dw_heap_data)) m3
  let m1 : L1Monad ProgramState := L1.seq (L1.seq (L1.guard p) (L1.modify dma_set_cap_mask)) m2
  -- Chain steps 4+5
  have hm4 := L1_seq_singleton_ok h4.1 h4.2 (m₂ := m5)
  have hm4_res : (m4 s3).results = {(Except.error (), s5)} := by
    dsimp [m4, m5]; rw [hm4.1, h5.1]
  have hm4_nf : ¬(m4 s3).failed := by
    dsimp [m4, m5]; intro hf; exact h5.2 (hm4.2.mp hf)
  -- Chain 3+4+5
  have hm3 := L1_seq_singleton_ok h3.1 h3.2 (m₂ := m4)
  have hm3_res : (m3 s2).results = {(Except.error (), s5)} := by
    dsimp [m3]; rw [hm3.1, hm4_res]
  have hm3_nf : ¬(m3 s2).failed := by
    dsimp [m3]; intro hf; exact hm4_nf (hm3.2.mp hf)
  -- Chain 2+3+4+5
  have hm2 := L1_seq_singleton_ok h2.1 h2.2 (m₂ := m3)
  have hm2_res : (m2 s1).results = {(Except.error (), s5)} := by
    dsimp [m2]; rw [hm2.1, hm3_res]
  have hm2_nf : ¬(m2 s1).failed := by
    dsimp [m2]; intro hf; exact hm3_nf (hm2.2.mp hf)
  -- Chain 1+2+3+4+5
  have hm1 := L1_seq_singleton_ok h1.1 h1.2 (m₂ := m2)
  have hm1_res : (m1 s).results = {(Except.error (), s5)} := by
    dsimp [m1]; rw [hm1.1, hm2_res]
  have hm1_nf : ¬(m1 s).failed := by
    dsimp [m1]; intro hf; exact hm2_nf (hm1.2.mp hf)
  -- Chain skip + body
  have h_skip := L1_seq_singleton_ok
    (show (L1.skip s).results = {(Except.ok (), s)} from rfl)
    (show ¬(L1.skip s).failed from not_false) (m₂ := m1)
  have h_body_res : (L1.seq L1.skip m1 s).results = {(Except.error (), s5)} := by
    rw [h_skip.1, hm1_res]
  have h_body_nf : ¬(L1.seq L1.skip m1 s).failed := by
    intro hf; exact hm1_nf (h_skip.2.mp hf)
  -- Catch converts error to ok
  have ⟨h_res, h_nf⟩ := L1_catch_error_singleton h_body_res h_body_nf
  constructor
  · exact h_nf
  · intro r s' h_mem _
    rw [h_res] at h_mem
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_mem
    exact dma_set_ret0_ret__val _

/-! ### dma_read proof -/

-- heapPtrValid preservation for read step functions
private theorem dma_set_cap_mask_ptrValid_out (s : ProgramState)
    (h : heapPtrValid s.globals.rawHeap s.locals.out) :
    heapPtrValid (dma_set_cap_mask s).globals.rawHeap (dma_set_cap_mask s).locals.out := by
  simp only [dma_set_cap_mask_globals, dma_set_cap_mask_out]; exact h

private theorem dma_set_cap_mask_ptrValid_data_read (s : ProgramState)
    (h : heapPtrValid s.globals.rawHeap
      (Ptr.elemOffset s.locals.data (hVal s.globals.rawHeap s.locals.buf).read_idx.toNat)) :
    heapPtrValid (dma_set_cap_mask s).globals.rawHeap
      (Ptr.elemOffset (dma_set_cap_mask s).locals.data
        (hVal (dma_set_cap_mask s).globals.rawHeap (dma_set_cap_mask s).locals.buf).read_idx.toNat) := by
  simp only [dma_set_cap_mask_globals, dma_set_cap_mask_data, dma_set_cap_mask_buf]; exact h

private theorem dr_heap_out_ptrValid_buf (s : ProgramState)
    (h : heapPtrValid s.globals.rawHeap s.locals.buf) :
    heapPtrValid (dr_heap_out s).globals.rawHeap (dr_heap_out s).locals.buf := by
  simp only [dr_heap_out_rawHeap, dr_heap_out_locals]
  exact heapUpdate_preserves_heapPtrValid _ _ _ _ h

private theorem dr_heap_read_idx_ptrValid_buf (s : ProgramState)
    (h : heapPtrValid s.globals.rawHeap s.locals.buf) :
    heapPtrValid (dr_heap_read_idx s).globals.rawHeap (dr_heap_read_idx s).locals.buf := by
  simp only [dr_heap_read_idx_rawHeap, dr_heap_read_idx_locals]
  exact heapUpdate_preserves_heapPtrValid _ _ _ _ h

private theorem dr_heap_count_ptrValid_buf (s : ProgramState)
    (h : heapPtrValid s.globals.rawHeap s.locals.buf) :
    heapPtrValid (dr_heap_count s).globals.rawHeap (dr_heap_count s).locals.buf := by
  simp only [dr_heap_count_rawHeap, dr_heap_count_locals]
  exact heapUpdate_preserves_heapPtrValid _ _ _ _ h

theorem dma_read_correct :
    dma_read_spec.satisfiedBy DmaBuffer.l1_dma_read_body := by
  suffices h : dma_read_spec.satisfiedBy l1_dma_read_manual from h
  unfold FuncSpec.satisfiedBy dma_read_spec validHoare
  intro s ⟨hbuf, hout, hdata, hcount⟩
  have hcond : decide ((hVal s.globals.rawHeap s.locals.buf).count = 0) = false := by
    rw [decide_eq_false_iff_not]
    intro heq; rw [heq] at hcount
    exact absurd hcount (by decide)
  unfold l1_dma_read_manual
  rw [L1_elim_cond_false
    (fun st : ProgramState => decide ((hVal st.globals.rawHeap st.locals.buf).count = 0)) hcond]
  -- After cond false: catch (seq skip rest) skip
  let p := fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.buf
  let po := fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.out
  let prd := fun s : ProgramState => heapPtrValid s.globals.rawHeap
    (Ptr.elemOffset s.locals.data (hVal s.globals.rawHeap s.locals.buf).read_idx.toNat)
  -- Intermediate states
  let s1 := dma_set_cap_mask s
  let s2 := dr_heap_out s1
  let s3 := dr_heap_read_idx s2
  let s4 := dr_heap_count s3
  let s5 := dma_set_ret0 s4
  -- heapPtrValid preservation
  have hbuf1 : p s1 := dma_set_cap_mask_ptrValid_buf s hbuf
  have hout1 : po s1 := dma_set_cap_mask_ptrValid_out s hout
  have hdata1 : prd s1 := dma_set_cap_mask_ptrValid_data_read s hdata
  have hbuf2 : p s2 := dr_heap_out_ptrValid_buf s1 hbuf1
  have hbuf3 : p s3 := dr_heap_read_idx_ptrValid_buf s2 hbuf2
  -- Step results
  have h1 := L1_guard_modify_result p dma_set_cap_mask s hbuf
  have h2 := L1_guard_guard_guard_modify_result po prd p dr_heap_out s1 hout1 hdata1 hbuf1
  have h3 := L1_guard_guard_modify_result p p dr_heap_read_idx s2 hbuf2 hbuf2
  have h4 := L1_guard_guard_modify_result p p dr_heap_count s3 hbuf3 hbuf3
  have h5 := L1_modify_throw_result dma_set_ret0 s4
  -- Define monad terms (matching the manual body structure)
  let m5 : L1Monad ProgramState := L1.seq (L1.modify dma_set_ret0) L1.throw
  let m4 : L1Monad ProgramState := L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify dr_heap_count))) m5
  let m3 : L1Monad ProgramState := L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify dr_heap_read_idx))) m4
  let m2 : L1Monad ProgramState := L1.seq (L1.seq (L1.guard po) (L1.seq (L1.guard prd) (L1.seq (L1.guard p) (L1.modify dr_heap_out)))) m3
  let m1 : L1Monad ProgramState := L1.seq (L1.seq (L1.guard p) (L1.modify dma_set_cap_mask)) m2
  -- Chain steps 4+5
  have hm4 := L1_seq_singleton_ok h4.1 h4.2 (m₂ := m5)
  have hm4_res : (m4 s3).results = {(Except.error (), s5)} := by
    dsimp [m4, m5]; rw [hm4.1, h5.1]
  have hm4_nf : ¬(m4 s3).failed := by
    dsimp [m4, m5]; intro hf; exact h5.2 (hm4.2.mp hf)
  -- Chain 3+4+5
  have hm3 := L1_seq_singleton_ok h3.1 h3.2 (m₂ := m4)
  have hm3_res : (m3 s2).results = {(Except.error (), s5)} := by
    dsimp [m3]; rw [hm3.1, hm4_res]
  have hm3_nf : ¬(m3 s2).failed := by
    dsimp [m3]; intro hf; exact hm4_nf (hm3.2.mp hf)
  -- Chain 2+3+4+5
  have hm2 := L1_seq_singleton_ok h2.1 h2.2 (m₂ := m3)
  have hm2_res : (m2 s1).results = {(Except.error (), s5)} := by
    dsimp [m2]; rw [hm2.1, hm3_res]
  have hm2_nf : ¬(m2 s1).failed := by
    dsimp [m2]; intro hf; exact hm3_nf (hm2.2.mp hf)
  -- Chain 1+2+3+4+5
  have hm1 := L1_seq_singleton_ok h1.1 h1.2 (m₂ := m2)
  have hm1_res : (m1 s).results = {(Except.error (), s5)} := by
    dsimp [m1]; rw [hm1.1, hm2_res]
  have hm1_nf : ¬(m1 s).failed := by
    dsimp [m1]; intro hf; exact hm2_nf (hm1.2.mp hf)
  -- Chain skip + body
  have h_skip := L1_seq_singleton_ok
    (show (L1.skip s).results = {(Except.ok (), s)} from rfl)
    (show ¬(L1.skip s).failed from not_false) (m₂ := m1)
  have h_body_res : (L1.seq L1.skip m1 s).results = {(Except.error (), s5)} := by
    rw [h_skip.1, hm1_res]
  have h_body_nf : ¬(L1.seq L1.skip m1 s).failed := by
    intro hf; exact hm1_nf (h_skip.2.mp hf)
  -- Catch converts error to ok
  have ⟨h_res, h_nf⟩ := L1_catch_error_singleton h_body_res h_body_nf
  constructor
  · exact h_nf
  · intro r s' h_mem _
    rw [h_res] at h_mem
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_mem
    exact dma_set_ret0_ret__val _
