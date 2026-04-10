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
  · sorry  -- modular arithmetic: (r + c) % cap + 1 ≡ (r + c + 1) % cap

/-- Invariant preserved by read (when count > 0). -/
theorem dma_read_preserves_inv (w r c cap : Nat)
    (h_inv : dmaInvariant w r c cap)
    (h_not_empty : c > 0) :
    dmaInvariant w ((r + 1) % cap) (c - 1) cap := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h_inv
  refine ⟨by omega, h2, Nat.mod_lt _ h4, h4, ?_⟩
  sorry  -- modular arithmetic reasoning

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

/-- dma_write: writes one element. Returns 0 on success, 1 if full. -/
def dma_write_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.buf ∧
    (hVal s.globals.rawHeap s.locals.buf).count <
      (hVal s.globals.rawHeap s.locals.buf).capacity
  post := fun r s =>
    r = Except.ok () →
    s.locals.ret__val = 0

/-- dma_read: reads one element. Returns 0 on success, 1 if empty. -/
def dma_read_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.buf ∧
    heapPtrValid s.globals.rawHeap s.locals.out ∧
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

theorem dma_init_correct :
    dma_init_spec.satisfiedBy DmaBuffer.l1_dma_init_body := by
  sorry

theorem dma_available_correct :
    dma_available_spec.satisfiedBy DmaBuffer.l1_dma_available_body := by
  sorry

theorem dma_write_correct :
    dma_write_spec.satisfiedBy DmaBuffer.l1_dma_write_body := by
  sorry

theorem dma_read_correct :
    dma_read_spec.satisfiedBy DmaBuffer.l1_dma_read_body := by
  sorry
