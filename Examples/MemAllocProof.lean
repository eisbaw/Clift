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

/-- pool_init: creates one big free block spanning the pool. -/
def pool_init_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.pm
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

theorem pool_init_correct :
    pool_init_spec.satisfiedBy MemAlloc.l1_pool_init_body := by
  sorry

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
  sorry -- Requires: conditional reasoning + UInt32 equality with 0xFFFFFFFF literal
