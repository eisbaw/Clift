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

private theorem L1_elim_cond_true {S : Type}
    (c : S → Bool) {t e m handler : L1Monad S} {s : S} (h : c s = true) :
    L1.catch (L1.seq (L1.condition c t e) m) handler s =
    L1.catch (L1.seq t m) handler s := by
  unfold L1.catch L1.seq L1.condition; simp [h]

private theorem L1_elim_cond_false {S : Type}
    (c : S → Bool) {t e m handler : L1Monad S} {s : S} (h : c s = false) :
    L1.catch (L1.seq (L1.condition c t e) m) handler s =
    L1.catch (L1.seq e m) handler s := by
  unfold L1.catch L1.seq L1.condition; simp [h]

private theorem L1_modify_throw_seq_catch_skip {S : Type}
    (f : S → S) (m2 : L1Monad S) (s : S) :
    (L1.catch (L1.seq (L1.seq (L1.modify f) L1.throw) m2) L1.skip s).results =
      {(Except.ok (), f s)} ∧
    ¬(L1.catch (L1.seq (L1.seq (L1.modify f) L1.throw) m2) L1.skip s).failed := by
  have h_mt := L1_modify_throw_result f s
  have h_inner_res : (L1.seq (L1.modify f) L1.throw s).results = {(Except.error (), f s)} := h_mt.1
  have h_inner_nf : ¬(L1.seq (L1.modify f) L1.throw s).failed := h_mt.2
  have h_outer := L1_seq_error_propagate h_inner_res h_inner_nf (m₂ := m2)
  exact L1_catch_error_singleton h_outer.1 h_outer.2

/-- Triple guard + modify result. -/
private theorem L1_guard_guard_guard_modify_result {S : Type}
    (p q r : S → Prop) [DecidablePred p] [DecidablePred q] [DecidablePred r]
    (f : S → S) (s : S) (hp : p s) (hq : q s) (hr : r s) :
    (L1.seq (L1.guard p) (L1.seq (L1.guard q) (L1.seq (L1.guard r) (L1.modify f))) s).results =
      {(Except.ok (), f s)} ∧
    ¬(L1.seq (L1.guard p) (L1.seq (L1.guard q) (L1.seq (L1.guard r) (L1.modify f))) s).failed := by
  have h_inner := L1_guard_modify_result r f s hr
  have h_mid := L1_seq_singleton_ok (L1_guard_results hq) (L1_guard_not_failed hq)
    (m₂ := L1.seq (L1.guard r) (L1.modify f))
  have h_mid_res : (L1.seq (L1.guard q) (L1.seq (L1.guard r) (L1.modify f)) s).results =
      {(Except.ok (), f s)} := by rw [h_mid.1, h_inner.1]
  have h_mid_nf : ¬(L1.seq (L1.guard q) (L1.seq (L1.guard r) (L1.modify f)) s).failed :=
    fun hf => h_inner.2 (h_mid.2.mp hf)
  have h_outer := L1_seq_singleton_ok (L1_guard_results hp) (L1_guard_not_failed hp)
    (m₂ := L1.seq (L1.guard q) (L1.seq (L1.guard r) (L1.modify f)))
  constructor
  · rw [h_outer.1, h_mid_res]
  · intro hf; exact h_mid_nf (h_outer.2.mp hf)

set_option maxRecDepth 8192 in
attribute [local irreducible] hVal heapPtrValid heapUpdate in
theorem dma_write_correct :
    dma_write_spec.satisfiedBy DmaBuffer.l1_dma_write_body := by
  unfold FuncSpec.satisfiedBy dma_write_spec validHoare
  intro s ⟨hbuf, hdata, hlt⟩
  -- The condition: count >= capacity. Since count < capacity, this is false.
  have hcond : decide ((hVal s.globals.rawHeap s.locals.buf).count >=
      (hVal s.globals.rawHeap s.locals.buf).capacity) = false := by
    simpa using hlt
  unfold DmaBuffer.l1_dma_write_body
  rw [L1_elim_cond_false
    (fun st : ProgramState => decide ((hVal st.globals.rawHeap st.locals.buf).count >=
      (hVal st.globals.rawHeap st.locals.buf).capacity)) hcond]
  -- After cond elimination: catch (seq skip rest) skip
  -- skip produces {(ok, s)}, then chain through rest
  let p := fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.buf
  let pd := fun s : ProgramState => heapPtrValid s.globals.rawHeap
    (Ptr.elemOffset s.locals.data (hVal s.globals.rawHeap s.locals.buf).write_idx.toNat)
  -- Step 1: guard(buf) + modify(cap_mask)
  let f1 := fun s : ProgramState =>
    { s with locals := { s.locals with cap_mask := (hVal s.globals.rawHeap s.locals.buf).capacity - 1 } }
  -- Step 2: guard(data[write_idx]) + modify(write value to data)
  let f2 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap :=
      (heapUpdate s.globals.rawHeap
        (Ptr.elemOffset s.locals.data (hVal s.globals.rawHeap s.locals.buf).write_idx.toNat)
        s.locals.value) } }
  -- Step 3: guard(buf) + guard(buf) + modify(write_idx := (write_idx + 1) &&& cap_mask)
  let f3 := fun s : ProgramState =>
    let newBuf : DmaBuffer.C_dma_buffer :=
      { hVal s.globals.rawHeap s.locals.buf with
        write_idx := ((hVal s.globals.rawHeap s.locals.buf).write_idx + 1) &&& s.locals.cap_mask }
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.buf newBuf } }
  -- Step 4: guard(buf) + guard(buf) + modify(count := count + 1)
  let f4 := fun s : ProgramState =>
    let newBuf : DmaBuffer.C_dma_buffer :=
      { hVal s.globals.rawHeap s.locals.buf with
        count := (hVal s.globals.rawHeap s.locals.buf).count + 1 }
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.buf newBuf } }
  -- Step 5: modify(ret=0) + throw
  let f5 := fun s : ProgramState =>
    { s with locals := { s.locals with ret__val := 0 } }
  -- Compute intermediate states
  let s1 := f1 s
  let s2 := f2 s1
  let s3 := f3 s2
  let s4 := f4 s3
  let s5 := f5 s4
  -- f1 only modifies locals, so heapPtrValid is preserved trivially
  have hbuf1 : p s1 := hbuf
  have hdata1 : pd s1 := hdata
  -- f2 writes to data element, buf ptr is still valid
  have hbuf2 : p s2 := heapUpdate_preserves_heapPtrValid _ _ _ _ hbuf1
  -- f3 writes to buf, buf ptr is still valid
  have hbuf3 : p s3 := heapUpdate_preserves_heapPtrValid _ _ _ _ hbuf2
  -- f4 writes to buf, buf ptr is still valid
  have hbuf4 : p s4 := heapUpdate_preserves_heapPtrValid _ _ _ _ hbuf3
  -- Step results
  have h1 := L1_guard_modify_result p f1 s hbuf
  have h2 := L1_guard_modify_result pd f2 s1 hdata1
  have h3 := L1_guard_guard_modify_result p p f3 s2 hbuf2 hbuf2
  have h4 := L1_guard_guard_modify_result p p f4 s3 hbuf3 hbuf3
  have h5 := L1_modify_throw_result f5 s4
  -- Chain step 4 and step 5
  have h45 := L1_seq_singleton_ok h4.1 h4.2
    (m₂ := L1.seq (L1.modify f5) L1.throw)
  have h45_res : (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f4)))
      (L1.seq (L1.modify f5) L1.throw) s3).results = {(Except.error (), s5)} := by
    rw [h45.1, h5.1]
  have h45_nf : ¬(L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f4)))
      (L1.seq (L1.modify f5) L1.throw) s3).failed :=
    fun hf => h5.2 (h45.2.mp hf)
  -- Chain step 3, 4, 5
  have h345 := L1_seq_singleton_ok h3.1 h3.2
    (m₂ := L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f4)))
      (L1.seq (L1.modify f5) L1.throw))
  have h345_res : (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f3)))
      (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f4)))
        (L1.seq (L1.modify f5) L1.throw)) s2).results = {(Except.error (), s5)} := by
    rw [h345.1, h45_res]
  have h345_nf : ¬(L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f3)))
      (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f4)))
        (L1.seq (L1.modify f5) L1.throw)) s2).failed :=
    fun hf => h45_nf (h345.2.mp hf)
  -- Chain step 2, 3, 4, 5
  have h2345 := L1_seq_singleton_ok h2.1 h2.2
    (m₂ := L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f3)))
      (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f4)))
        (L1.seq (L1.modify f5) L1.throw)))
  have h2345_res : (L1.seq (L1.seq (L1.guard pd) (L1.modify f2))
      (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f3)))
        (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f4)))
          (L1.seq (L1.modify f5) L1.throw))) s1).results = {(Except.error (), s5)} := by
    rw [h2345.1, h345_res]
  have h2345_nf : ¬(L1.seq (L1.seq (L1.guard pd) (L1.modify f2))
      (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f3)))
        (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f4)))
          (L1.seq (L1.modify f5) L1.throw))) s1).failed :=
    fun hf => h345_nf (h2345.2.mp hf)
  -- Chain step 1, 2, 3, 4, 5
  have h12345 := L1_seq_singleton_ok h1.1 h1.2
    (m₂ := L1.seq (L1.seq (L1.guard pd) (L1.modify f2))
      (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f3)))
        (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f4)))
          (L1.seq (L1.modify f5) L1.throw))))
  have h12345_res : (L1.seq (L1.seq (L1.guard p) (L1.modify f1))
      (L1.seq (L1.seq (L1.guard pd) (L1.modify f2))
        (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f3)))
          (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f4)))
            (L1.seq (L1.modify f5) L1.throw)))) s).results = {(Except.error (), s5)} := by
    rw [h12345.1, h2345_res]
  have h12345_nf : ¬(L1.seq (L1.seq (L1.guard p) (L1.modify f1))
      (L1.seq (L1.seq (L1.guard pd) (L1.modify f2))
        (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f3)))
          (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f4)))
            (L1.seq (L1.modify f5) L1.throw)))) s).failed :=
    fun hf => h2345_nf (h12345.2.mp hf)
  -- Now chain with skip (from the condition elimination)
  have h_skip_res : (L1.skip s).results = {(Except.ok (), s)} := rfl
  have h_skip_nf : ¬(L1.skip s).failed := not_false
  have h_body := L1_seq_singleton_ok h_skip_res h_skip_nf
    (m₂ := L1.seq (L1.seq (L1.guard p) (L1.modify f1))
      (L1.seq (L1.seq (L1.guard pd) (L1.modify f2))
        (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f3)))
          (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f4)))
            (L1.seq (L1.modify f5) L1.throw)))))
  have h_body_res : (L1.seq L1.skip
      (L1.seq (L1.seq (L1.guard p) (L1.modify f1))
        (L1.seq (L1.seq (L1.guard pd) (L1.modify f2))
          (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f3)))
            (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f4)))
              (L1.seq (L1.modify f5) L1.throw))))) s).results = {(Except.error (), s5)} := by
    rw [h_body.1, h12345_res]
  have h_body_nf : ¬(L1.seq L1.skip
      (L1.seq (L1.seq (L1.guard p) (L1.modify f1))
        (L1.seq (L1.seq (L1.guard pd) (L1.modify f2))
          (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f3)))
            (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f4)))
              (L1.seq (L1.modify f5) L1.throw))))) s).failed :=
    fun hf => h12345_nf (h_body.2.mp hf)
  -- Catch turns error into ok
  have ⟨h_res, h_nf⟩ := L1_catch_error_singleton h_body_res h_body_nf
  constructor
  · exact h_nf
  · intro r s' h_mem
    rw [h_res] at h_mem
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_mem
    intro _
    -- s5 = { s4 with locals.ret__val := 0 }
    show s5.locals.ret__val = 0
    rfl

set_option maxRecDepth 8192 in
attribute [local irreducible] hVal heapPtrValid heapUpdate in
theorem dma_read_correct :
    dma_read_spec.satisfiedBy DmaBuffer.l1_dma_read_body := by
  unfold FuncSpec.satisfiedBy dma_read_spec validHoare
  intro s ⟨hbuf, hout, hdata, hcount⟩
  -- The condition: count = 0. Since count > 0, this is false.
  have hcond : decide ((hVal s.globals.rawHeap s.locals.buf).count = 0) = false := by
    simp only [decide_eq_false_iff_not]
    intro heq; rw [heq] at hcount; exact absurd hcount (by simp)
  unfold DmaBuffer.l1_dma_read_body
  rw [L1_elim_cond_false
    (fun st : ProgramState => decide ((hVal st.globals.rawHeap st.locals.buf).count = 0)) hcond]
  -- After cond elimination: catch (seq skip rest) skip
  let p := fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.buf
  let po := fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.out
  let pd := fun s : ProgramState => heapPtrValid s.globals.rawHeap
    (Ptr.elemOffset s.locals.data (hVal s.globals.rawHeap s.locals.buf).read_idx.toNat)
  -- Step 1: guard(buf) + modify(cap_mask)
  let f1 := fun s : ProgramState =>
    { s with locals := { s.locals with cap_mask := (hVal s.globals.rawHeap s.locals.buf).capacity - 1 } }
  -- Step 2: guard(out) + guard(data[read_idx]) + guard(buf) + modify(heapUpdate out := data[read_idx])
  let f2 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap :=
      (heapUpdate s.globals.rawHeap s.locals.out
        (hVal s.globals.rawHeap
          (Ptr.elemOffset s.locals.data (hVal s.globals.rawHeap s.locals.buf).read_idx.toNat))) } }
  -- Step 3: guard(buf) + guard(buf) + modify(read_idx := (read_idx + 1) &&& cap_mask)
  let f3 := fun s : ProgramState =>
    let newBuf : DmaBuffer.C_dma_buffer :=
      { hVal s.globals.rawHeap s.locals.buf with
        read_idx := ((hVal s.globals.rawHeap s.locals.buf).read_idx + 1) &&& s.locals.cap_mask }
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.buf newBuf } }
  -- Step 4: guard(buf) + guard(buf) + modify(count := count - 1)
  let f4 := fun s : ProgramState =>
    let newBuf : DmaBuffer.C_dma_buffer :=
      { hVal s.globals.rawHeap s.locals.buf with
        count := (hVal s.globals.rawHeap s.locals.buf).count - 1 }
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.buf newBuf } }
  -- Step 5: modify(ret=0) + throw
  let f5 := fun s : ProgramState =>
    { s with locals := { s.locals with ret__val := 0 } }
  -- Compute intermediate states
  let s1 := f1 s
  let s2 := f2 s1
  let s3 := f3 s2
  let s4 := f4 s3
  let s5 := f5 s4
  -- f1 only modifies locals, so heapPtrValid is preserved trivially
  have hbuf1 : p s1 := hbuf
  have hout1 : po s1 := hout
  have hdata1 : pd s1 := hdata
  -- f2 writes to out, buf and data ptrs are still valid
  have hbuf2 : p s2 := heapUpdate_preserves_heapPtrValid _ _ _ _ hbuf1
  -- f3 writes to buf, buf ptr is still valid
  have hbuf3 : p s3 := heapUpdate_preserves_heapPtrValid _ _ _ _ hbuf2
  -- f4 writes to buf, buf ptr is still valid
  have hbuf4 : p s4 := heapUpdate_preserves_heapPtrValid _ _ _ _ hbuf3
  -- Step results
  have h1 := L1_guard_modify_result p f1 s hbuf
  have h2 := L1_guard_guard_guard_modify_result po pd p f2 s1 hout1 hdata1 hbuf1
  have h3 := L1_guard_guard_modify_result p p f3 s2 hbuf2 hbuf2
  have h4 := L1_guard_guard_modify_result p p f4 s3 hbuf3 hbuf3
  have h5 := L1_modify_throw_result f5 s4
  -- Chain step 4 and step 5
  have h45 := L1_seq_singleton_ok h4.1 h4.2
    (m₂ := L1.seq (L1.modify f5) L1.throw)
  have h45_res : (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f4)))
      (L1.seq (L1.modify f5) L1.throw) s3).results = {(Except.error (), s5)} := by
    rw [h45.1, h5.1]
  have h45_nf : ¬(L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f4)))
      (L1.seq (L1.modify f5) L1.throw) s3).failed :=
    fun hf => h5.2 (h45.2.mp hf)
  -- Chain step 3, 4, 5
  have h345 := L1_seq_singleton_ok h3.1 h3.2
    (m₂ := L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f4)))
      (L1.seq (L1.modify f5) L1.throw))
  have h345_res : (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f3)))
      (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f4)))
        (L1.seq (L1.modify f5) L1.throw)) s2).results = {(Except.error (), s5)} := by
    rw [h345.1, h45_res]
  have h345_nf : ¬(L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f3)))
      (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f4)))
        (L1.seq (L1.modify f5) L1.throw)) s2).failed :=
    fun hf => h45_nf (h345.2.mp hf)
  -- Chain step 2, 3, 4, 5
  have h2345 := L1_seq_singleton_ok h2.1 h2.2
    (m₂ := L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f3)))
      (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f4)))
        (L1.seq (L1.modify f5) L1.throw)))
  have h2345_res : (L1.seq
      (L1.seq (L1.guard po) (L1.seq (L1.guard pd) (L1.seq (L1.guard p) (L1.modify f2))))
      (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f3)))
        (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f4)))
          (L1.seq (L1.modify f5) L1.throw))) s1).results = {(Except.error (), s5)} := by
    rw [h2345.1, h345_res]
  have h2345_nf : ¬(L1.seq
      (L1.seq (L1.guard po) (L1.seq (L1.guard pd) (L1.seq (L1.guard p) (L1.modify f2))))
      (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f3)))
        (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f4)))
          (L1.seq (L1.modify f5) L1.throw))) s1).failed :=
    fun hf => h345_nf (h2345.2.mp hf)
  -- Chain step 1, 2, 3, 4, 5
  have h12345 := L1_seq_singleton_ok h1.1 h1.2
    (m₂ := L1.seq
      (L1.seq (L1.guard po) (L1.seq (L1.guard pd) (L1.seq (L1.guard p) (L1.modify f2))))
      (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f3)))
        (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f4)))
          (L1.seq (L1.modify f5) L1.throw))))
  have h12345_res : (L1.seq (L1.seq (L1.guard p) (L1.modify f1))
      (L1.seq
        (L1.seq (L1.guard po) (L1.seq (L1.guard pd) (L1.seq (L1.guard p) (L1.modify f2))))
        (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f3)))
          (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f4)))
            (L1.seq (L1.modify f5) L1.throw)))) s).results = {(Except.error (), s5)} := by
    rw [h12345.1, h2345_res]
  have h12345_nf : ¬(L1.seq (L1.seq (L1.guard p) (L1.modify f1))
      (L1.seq
        (L1.seq (L1.guard po) (L1.seq (L1.guard pd) (L1.seq (L1.guard p) (L1.modify f2))))
        (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f3)))
          (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f4)))
            (L1.seq (L1.modify f5) L1.throw)))) s).failed :=
    fun hf => h2345_nf (h12345.2.mp hf)
  -- Now chain with skip (from the condition elimination)
  have h_skip_res : (L1.skip s).results = {(Except.ok (), s)} := rfl
  have h_skip_nf : ¬(L1.skip s).failed := not_false
  have h_body := L1_seq_singleton_ok h_skip_res h_skip_nf
    (m₂ := L1.seq (L1.seq (L1.guard p) (L1.modify f1))
      (L1.seq
        (L1.seq (L1.guard po) (L1.seq (L1.guard pd) (L1.seq (L1.guard p) (L1.modify f2))))
        (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f3)))
          (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f4)))
            (L1.seq (L1.modify f5) L1.throw)))))
  have h_body_res : (L1.seq L1.skip
      (L1.seq (L1.seq (L1.guard p) (L1.modify f1))
        (L1.seq
          (L1.seq (L1.guard po) (L1.seq (L1.guard pd) (L1.seq (L1.guard p) (L1.modify f2))))
          (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f3)))
            (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f4)))
              (L1.seq (L1.modify f5) L1.throw))))) s).results = {(Except.error (), s5)} := by
    rw [h_body.1, h12345_res]
  have h_body_nf : ¬(L1.seq L1.skip
      (L1.seq (L1.seq (L1.guard p) (L1.modify f1))
        (L1.seq
          (L1.seq (L1.guard po) (L1.seq (L1.guard pd) (L1.seq (L1.guard p) (L1.modify f2))))
          (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f3)))
            (L1.seq (L1.seq (L1.guard p) (L1.seq (L1.guard p) (L1.modify f4)))
              (L1.seq (L1.modify f5) L1.throw))))) s).failed :=
    fun hf => h12345_nf (h_body.2.mp hf)
  -- Catch turns error into ok
  have ⟨h_res, h_nf⟩ := L1_catch_error_singleton h_body_res h_body_nf
  constructor
  · exact h_nf
  · intro r s' h_mem
    rw [h_res] at h_mem
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_mem
    intro _
    show s5.locals.ret__val = 0
    rfl
