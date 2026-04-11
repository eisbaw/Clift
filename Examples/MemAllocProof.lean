-- Task 0158: Memory allocator verification
--
-- First-fit allocator with explicit free list.
-- 6 functions imported from mem_alloc.c (~130 LOC C -> ~541 lines Lean).
--
-- Key verification targets:
-- - Free list invariant: all free blocks on the list
-- - Allocated blocks don't overlap
-- - pool_free returns block to free list
-- - Total allocation bounded by pool size
-- - No double-free (allocated flag check)

import Generated.MemAlloc
import Clift.Lifting.Pipeline
import Clift.Lifting.FuncSpec

set_option maxHeartbeats 12800000
set_option maxRecDepth 4096

open MemAlloc

/-! # Step 1: Run the clift pipeline on all 6 functions -/

clift MemAlloc

/-! # Step 2: Verify L1 definitions exist -/

#check @MemAlloc.l1_pool_init_body
#check @MemAlloc.l1_pool_malloc_body
#check @MemAlloc.l1_pool_free_body
#check @MemAlloc.l1_pool_allocated_body
#check @MemAlloc.l1_pool_alloc_count_body
#check @MemAlloc.l1_pool_has_free_body

/-! # Step 3: Free list invariant

The key data structure invariant for a memory allocator:
1. Every free block is on the free list (reachable from free_head)
2. Every block on the free list has allocated = 0
3. No two blocks overlap
4. total_allocated = sum of sizes of all allocated blocks
5. total_allocated <= pool_size

We state this as a Lean predicate on the abstract pool state. -/

/-- Abstract model of a memory pool block. -/
structure PoolBlock where
  offset : Nat       -- start index in pool
  size : Nat         -- total size including header
  allocated : Bool   -- is this block allocated?
  deriving Repr

/-- Pool invariant: well-formed free list + allocation tracking. -/
def poolInvariant (blocks : List PoolBlock) (freeHead : Nat)
    (totalAlloc : Nat) (poolSize : Nat) : Prop :=
  -- All block sizes are positive
  (∀ b ∈ blocks, b.size ≥ 6) ∧
  -- Blocks don't overlap: sorted by offset, no gaps or overlaps
  (∀ b1 b2, b1 ∈ blocks → b2 ∈ blocks → b1 ≠ b2 →
    b1.offset + b1.size ≤ b2.offset ∨ b2.offset + b2.size ≤ b1.offset) ∧
  -- Total allocation bounded
  totalAlloc ≤ poolSize ∧
  -- All blocks fit in pool
  (∀ b ∈ blocks, b.offset + b.size ≤ poolSize)

/-! # Step 4: FuncSpecs -/

/-- pool_init: creates one big free block spanning the pool.
    Precondition requires heapPtrValid for both the pool array (first 3 elements)
    and the pool manager struct (pm). The C code writes to pool[0..2] (block header)
    and pm fields (free_head, total_allocated, alloc_count, pool_size). -/
def pool_init_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.pm ∧
    heapPtrValid s.globals.rawHeap (Ptr.elemOffset s.locals.pool 0) ∧
    heapPtrValid s.globals.rawHeap (Ptr.elemOffset s.locals.pool 1) ∧
    heapPtrValid s.globals.rawHeap (Ptr.elemOffset s.locals.pool 2)
  post := fun r s =>
    r = Except.ok () →
    let pmv := hVal s.globals.rawHeap s.locals.pm
    pmv.free_head = 0 ∧
    pmv.total_allocated = 0 ∧
    pmv.alloc_count = 0 ∧
    pmv.pool_size = s.locals.pool_size

/-- pool_allocated: returns total_allocated field. -/
def pool_allocated_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.pm
  post := fun r s =>
    r = Except.ok () →
    s.locals.ret__val = (hVal s.globals.rawHeap s.locals.pm).total_allocated

/-- pool_alloc_count: returns alloc_count field. -/
def pool_alloc_count_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.pm
  post := fun r s =>
    r = Except.ok () →
    s.locals.ret__val = (hVal s.globals.rawHeap s.locals.pm).alloc_count

/-- pool_has_free: checks if free_head is not null. -/
def pool_has_free_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.pm
  post := fun r s =>
    r = Except.ok () →
    let pmv := hVal s.globals.rawHeap s.locals.pm
    (pmv.free_head ≠ 0xFFFFFFFF → s.locals.ret__val = 1) ∧
    (pmv.free_head = 0xFFFFFFFF → s.locals.ret__val = 0)

/-- pool_free: returns block to free list.
    Key: checks allocated flag to prevent double-free. -/
def pool_free_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.pm ∧
    s.locals.ptr >= 3 ∧
    s.locals.ptr < (hVal s.globals.rawHeap s.locals.pm).pool_size
  post := fun r s =>
    r = Except.ok () →
    -- Returns 0 on success, 1 on error
    (s.locals.ret__val = 0 ∨ s.locals.ret__val = 1)

/-! # Step 5: validHoare theorems -/

/-! ## pool_init: 8-step init with inline L1 result computation -/

theorem pool_init_correct :
    pool_init_spec.satisfiedBy MemAlloc.l1_pool_init_body := by
  unfold FuncSpec.satisfiedBy pool_init_spec validHoare
  intro s ⟨hv_pm, hv_p0, hv_p1, hv_p2⟩
  let f1 := fun s : ProgramState => { s with locals := { s.locals with hdr_idx := 0 } }
  let p0 := fun s : ProgramState => heapPtrValid s.globals.rawHeap (Ptr.elemOffset s.locals.pool s.locals.hdr_idx.toNat)
  let f2 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap (Ptr.elemOffset s.locals.pool s.locals.hdr_idx.toNat) s.locals.pool_size } }
  let p1 := fun s : ProgramState => heapPtrValid s.globals.rawHeap (Ptr.elemOffset s.locals.pool (s.locals.hdr_idx + 1).toNat)
  let f3 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap (Ptr.elemOffset s.locals.pool (s.locals.hdr_idx + 1).toNat) (4294967295 : UInt32) } }
  let p2 := fun s : ProgramState => heapPtrValid s.globals.rawHeap (Ptr.elemOffset s.locals.pool (s.locals.hdr_idx + 2).toNat)
  let f4 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap (Ptr.elemOffset s.locals.pool (s.locals.hdr_idx + 2).toNat) (0 : UInt32) } }
  let ppm := fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.pm
  let f5 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.pm ({ hVal s.globals.rawHeap s.locals.pm with free_head := 0 } : C_mem_pool) } }
  let f6 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.pm ({ hVal s.globals.rawHeap s.locals.pm with total_allocated := 0 } : C_mem_pool) } }
  let f7 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.pm ({ hVal s.globals.rawHeap s.locals.pm with alloc_count := 0 } : C_mem_pool) } }
  let f8 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.pm ({ hVal s.globals.rawHeap s.locals.pm with pool_size := s.locals.pool_size } : C_mem_pool) } }
  let s1 := f1 s; let s2 := f2 s1; let s3 := f3 s2; let s4 := f4 s3
  let s5 := f5 s4; let s6 := f6 s5; let s7 := f7 s6; let s8 := f8 s7
  -- Guard validity
  have hv1 : p0 s1 := hv_p0
  have hv2 : p1 s2 := heapUpdate_preserves_heapPtrValid _ _ _ _ hv_p1
  have hv3 : p2 s3 := heapUpdate_preserves_heapPtrValid _ _ _ _ (heapUpdate_preserves_heapPtrValid _ _ _ _ hv_p2)
  have hv4 : ppm s4 := heapUpdate_preserves_heapPtrValid _ _ _ _ (heapUpdate_preserves_heapPtrValid _ _ _ _ (heapUpdate_preserves_heapPtrValid _ _ _ _ hv_pm))
  have hv5 : ppm s5 := heapUpdate_preserves_heapPtrValid _ _ _ _ hv4
  have hv6 : ppm s6 := heapUpdate_preserves_heapPtrValid _ _ _ _ hv5
  have hv7 : ppm s7 := heapUpdate_preserves_heapPtrValid _ _ _ _ hv6
  -- Step results
  have h1r : (L1.modify f1 s).results = {(Except.ok (), s1)} := rfl
  have h1n : ¬(L1.modify f1 s).failed := not_false
  have h2 := L1_guard_modify_result p0 f2 s1 hv1
  have h3 := L1_guard_modify_result p1 f3 s2 hv2
  have h4 := L1_guard_modify_result p2 f4 s3 hv3
  have h5 := L1_guard_modify_result ppm f5 s4 hv4
  have h6 := L1_guard_modify_result ppm f6 s5 hv5
  have h7 := L1_guard_modify_result ppm f7 s6 hv6
  have h8 := L1_guard_modify_result ppm f8 s7 hv7
  -- Chain 7,8
  have c78 := L1_seq_singleton_ok h7.1 h7.2 (m₂ := L1.seq (L1.guard ppm) (L1.modify f8))
  have c78r : (L1.seq (L1.seq (L1.guard ppm) (L1.modify f7)) (L1.seq (L1.guard ppm) (L1.modify f8)) s6).results = {(Except.ok (), s8)} := by rw [c78.1, h8.1]
  have c78n : ¬(L1.seq (L1.seq (L1.guard ppm) (L1.modify f7)) (L1.seq (L1.guard ppm) (L1.modify f8)) s6).failed := fun h => h8.2 (c78.2.mp h)
  -- Chain 6-8
  have c678 := L1_seq_singleton_ok h6.1 h6.2 (m₂ := L1.seq (L1.seq (L1.guard ppm) (L1.modify f7)) (L1.seq (L1.guard ppm) (L1.modify f8)))
  have c678r : (L1.seq (L1.seq (L1.guard ppm) (L1.modify f6)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f7)) (L1.seq (L1.guard ppm) (L1.modify f8))) s5).results = {(Except.ok (), s8)} := by rw [c678.1, c78r]
  have c678n : ¬(L1.seq (L1.seq (L1.guard ppm) (L1.modify f6)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f7)) (L1.seq (L1.guard ppm) (L1.modify f8))) s5).failed := fun h => c78n (c678.2.mp h)
  -- Chain 5-8
  have c5678 := L1_seq_singleton_ok h5.1 h5.2 (m₂ := L1.seq (L1.seq (L1.guard ppm) (L1.modify f6)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f7)) (L1.seq (L1.guard ppm) (L1.modify f8))))
  have c5678r : (L1.seq (L1.seq (L1.guard ppm) (L1.modify f5)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f6)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f7)) (L1.seq (L1.guard ppm) (L1.modify f8)))) s4).results = {(Except.ok (), s8)} := by rw [c5678.1, c678r]
  have c5678n : ¬(L1.seq (L1.seq (L1.guard ppm) (L1.modify f5)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f6)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f7)) (L1.seq (L1.guard ppm) (L1.modify f8)))) s4).failed := fun h => c678n (c5678.2.mp h)
  -- Chain 4-8
  have c45678 := L1_seq_singleton_ok h4.1 h4.2 (m₂ := L1.seq (L1.seq (L1.guard ppm) (L1.modify f5)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f6)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f7)) (L1.seq (L1.guard ppm) (L1.modify f8)))))
  have c45678r : (L1.seq (L1.seq (L1.guard p2) (L1.modify f4)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f5)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f6)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f7)) (L1.seq (L1.guard ppm) (L1.modify f8))))) s3).results = {(Except.ok (), s8)} := by rw [c45678.1, c5678r]
  have c45678n : ¬(L1.seq (L1.seq (L1.guard p2) (L1.modify f4)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f5)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f6)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f7)) (L1.seq (L1.guard ppm) (L1.modify f8))))) s3).failed := fun h => c5678n (c45678.2.mp h)
  -- Chain 3-8
  have c345678 := L1_seq_singleton_ok h3.1 h3.2 (m₂ := L1.seq (L1.seq (L1.guard p2) (L1.modify f4)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f5)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f6)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f7)) (L1.seq (L1.guard ppm) (L1.modify f8))))))
  have c345678r : (L1.seq (L1.seq (L1.guard p1) (L1.modify f3)) (L1.seq (L1.seq (L1.guard p2) (L1.modify f4)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f5)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f6)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f7)) (L1.seq (L1.guard ppm) (L1.modify f8)))))) s2).results = {(Except.ok (), s8)} := by rw [c345678.1, c45678r]
  have c345678n : ¬(L1.seq (L1.seq (L1.guard p1) (L1.modify f3)) (L1.seq (L1.seq (L1.guard p2) (L1.modify f4)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f5)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f6)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f7)) (L1.seq (L1.guard ppm) (L1.modify f8)))))) s2).failed := fun h => c45678n (c345678.2.mp h)
  -- Chain 2-8
  have c2345678 := L1_seq_singleton_ok h2.1 h2.2 (m₂ := L1.seq (L1.seq (L1.guard p1) (L1.modify f3)) (L1.seq (L1.seq (L1.guard p2) (L1.modify f4)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f5)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f6)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f7)) (L1.seq (L1.guard ppm) (L1.modify f8)))))))
  have c2345678r : (L1.seq (L1.seq (L1.guard p0) (L1.modify f2)) (L1.seq (L1.seq (L1.guard p1) (L1.modify f3)) (L1.seq (L1.seq (L1.guard p2) (L1.modify f4)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f5)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f6)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f7)) (L1.seq (L1.guard ppm) (L1.modify f8))))))) s1).results = {(Except.ok (), s8)} := by rw [c2345678.1, c345678r]
  have c2345678n : ¬(L1.seq (L1.seq (L1.guard p0) (L1.modify f2)) (L1.seq (L1.seq (L1.guard p1) (L1.modify f3)) (L1.seq (L1.seq (L1.guard p2) (L1.modify f4)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f5)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f6)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f7)) (L1.seq (L1.guard ppm) (L1.modify f8))))))) s1).failed := fun h => c345678n (c2345678.2.mp h)
  -- Chain 1-8
  have c_all := L1_seq_singleton_ok h1r h1n (m₂ := L1.seq (L1.seq (L1.guard p0) (L1.modify f2)) (L1.seq (L1.seq (L1.guard p1) (L1.modify f3)) (L1.seq (L1.seq (L1.guard p2) (L1.modify f4)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f5)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f6)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f7)) (L1.seq (L1.guard ppm) (L1.modify f8))))))))
  have c_all_r : (L1.seq (L1.modify f1) (L1.seq (L1.seq (L1.guard p0) (L1.modify f2)) (L1.seq (L1.seq (L1.guard p1) (L1.modify f3)) (L1.seq (L1.seq (L1.guard p2) (L1.modify f4)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f5)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f6)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f7)) (L1.seq (L1.guard ppm) (L1.modify f8)))))))) s).results = {(Except.ok (), s8)} := by rw [c_all.1, c2345678r]
  have c_all_n : ¬(L1.seq (L1.modify f1) (L1.seq (L1.seq (L1.guard p0) (L1.modify f2)) (L1.seq (L1.seq (L1.guard p1) (L1.modify f3)) (L1.seq (L1.seq (L1.guard p2) (L1.modify f4)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f5)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f6)) (L1.seq (L1.seq (L1.guard ppm) (L1.modify f7)) (L1.seq (L1.guard ppm) (L1.modify f8)))))))) s).failed := fun h => c2345678n (c_all.2.mp h)
  -- Catch wrapper
  have h_catch := L1_catch_singleton_ok c_all_r c_all_n
  unfold MemAlloc.l1_pool_init_body
  constructor
  · exact h_catch.2
  · intro r s' h_mem
    rw [h_catch.1] at h_mem
    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
    subst hr; subst hs
    intro _
    -- Chain hVal_heapUpdate_same for pm fields (steps 5-8)
    have hb4 := heapPtrValid_bound hv4
    have hb5 := heapPtrValid_bound hv5
    have hb6 := heapPtrValid_bound hv6
    have hb7 := heapPtrValid_bound hv7
    have h8v : hVal s8.globals.rawHeap s8.locals.pm =
        ({ hVal s7.globals.rawHeap s7.locals.pm with pool_size := s7.locals.pool_size } : C_mem_pool) :=
      hVal_heapUpdate_same _ _ _ hb7
    have h7v : hVal s7.globals.rawHeap s7.locals.pm =
        ({ hVal s6.globals.rawHeap s6.locals.pm with alloc_count := 0 } : C_mem_pool) :=
      hVal_heapUpdate_same _ _ _ hb6
    have h6v : hVal s6.globals.rawHeap s6.locals.pm =
        ({ hVal s5.globals.rawHeap s5.locals.pm with total_allocated := 0 } : C_mem_pool) :=
      hVal_heapUpdate_same _ _ _ hb5
    have h5v : hVal s5.globals.rawHeap s5.locals.pm =
        ({ hVal s4.globals.rawHeap s4.locals.pm with free_head := 0 } : C_mem_pool) :=
      hVal_heapUpdate_same _ _ _ hb4
    rw [h8v, h7v, h6v, h5v]
    exact ⟨rfl, rfl, rfl, rfl⟩

private theorem ma_retval_globals (s : ProgramState) (v : UInt32) :
    ({ s with locals := { s.locals with ret__val := v } } : ProgramState).globals = s.globals := rfl
private theorem ma_retval_pm (s : ProgramState) (v : UInt32) :
    ({ s with locals := { s.locals with ret__val := v } } : ProgramState).locals.pm = s.locals.pm := rfl
private theorem ma_retval_val (s : ProgramState) (v : UInt32) :
    ({ s with locals := { s.locals with ret__val := v } } : ProgramState).locals.ret__val = v := rfl

attribute [local irreducible] hVal heapPtrValid in
theorem pool_allocated_correct :
    pool_allocated_spec.satisfiedBy MemAlloc.l1_pool_allocated_body := by
  unfold FuncSpec.satisfiedBy pool_allocated_spec validHoare
  intro s hpre
  unfold MemAlloc.l1_pool_allocated_body
  have h := L1_guard_modify_throw_catch_skip_result
    (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.pm)
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := (hVal s.globals.rawHeap s.locals.pm).total_allocated } })
    s hpre
  obtain ⟨h_res, h_nf⟩ := h
  constructor
  · exact h_nf
  · intro r s' h_mem _
    rw [h_res] at h_mem
    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
    subst hr; subst hs
    rw [ma_retval_val, ma_retval_globals, ma_retval_pm]

attribute [local irreducible] hVal heapPtrValid in
theorem pool_alloc_count_correct :
    pool_alloc_count_spec.satisfiedBy MemAlloc.l1_pool_alloc_count_body := by
  unfold FuncSpec.satisfiedBy pool_alloc_count_spec validHoare
  intro s hpre
  unfold MemAlloc.l1_pool_alloc_count_body
  have h := L1_guard_modify_throw_catch_skip_result
    (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.pm)
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := (hVal s.globals.rawHeap s.locals.pm).alloc_count } })
    s hpre
  obtain ⟨h_res, h_nf⟩ := h
  constructor
  · exact h_nf
  · intro r s' h_mem _
    rw [h_res] at h_mem
    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
    subst hr; subst hs
    rw [ma_retval_val, ma_retval_globals, ma_retval_pm]

theorem pool_has_free_correct :
    pool_has_free_spec.satisfiedBy MemAlloc.l1_pool_has_free_body := by
  unfold FuncSpec.satisfiedBy pool_has_free_spec validHoare
  intro s hpre
  unfold MemAlloc.l1_pool_has_free_body
  have h := L1_guard_modify_throw_catch_skip_result
    (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.pm)
    (fun s : ProgramState =>
      { s with locals := { s.locals with ret__val := (if (hVal s.globals.rawHeap s.locals.pm).free_head != 0xFFFFFFFF then 1 else 0) } })
    s hpre
  obtain ⟨h_res, h_nf⟩ := h
  refine ⟨h_nf, fun r s' h_mem _ => ?_⟩
  rw [h_res] at h_mem
  obtain ⟨hr, hs⟩ := Prod.mk.inj h_mem
  subst hr
  have h_ret :
      s'.locals.ret__val = (if (hVal s.globals.rawHeap s.locals.pm).free_head != 0xFFFFFFFF then 1 else 0) :=
    hs ▸ ma_retval_val s _
  have h_glob : s'.globals = s.globals := hs ▸ ma_retval_globals s _
  have h_pm : s'.locals.pm = s.locals.pm := hs ▸ ma_retval_pm s _
  rw [h_glob, h_pm]
  constructor
  · intro hne
    rw [h_ret]
    simp [hne]
  · intro heq
    rw [h_ret]
    simp [heq]
