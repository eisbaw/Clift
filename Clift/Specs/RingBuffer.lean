-- RingBuffer: Reusable abstract specification for a circular buffer
--
-- Abstract state: circular buffer with head/tail indices and count.
-- Operations: write, read, peek, size, isEmpty, isFull, clear.
-- Key properties: write/read count balance, bounded size.
--
-- For linked-list-based queues, use Specs.Queue instead.

import Clift.Lifting.AbstractSpec

namespace Specs.RingBuffer

/-- Abstract state for a circular buffer.
    Uses Nat indices and count; the invariant enforces bounds. -/
structure RingBufState where
  /-- Read index (head) -/
  head : Nat
  /-- Write index (tail) -/
  tail : Nat
  /-- Number of elements currently stored -/
  count : Nat
  /-- Buffer capacity -/
  capacity : Nat
  deriving Repr

/-- Operations on the ring buffer. -/
inductive RingBufOp where
  | write
  | read
  | peek
  | size
  | isEmpty
  | isFull
  | clear

/-- Abstract specification for a circular buffer.
    Properties about modular index arithmetic are left to the instantiation
    since they depend on the concrete C implementation's index wrapping. -/
@[reducible] def ringBufSpec (cap : Nat) (_hcap : cap > 0) :
    AbstractSpec RingBufState RingBufOp where
  init := fun s => s.count = 0 ∧ s.head = 0 ∧ s.tail = 0 ∧ s.capacity = cap
  opSpec := fun op => match op with
    | .write => {
        pre := fun s => s.count < s.capacity
        post := fun s s' =>
          s'.count = s.count + 1 ∧
          s'.capacity = s.capacity
      }
    | .read => {
        pre := fun s => s.count > 0
        post := fun s s' =>
          s'.count = s.count - 1 ∧
          s'.capacity = s.capacity
      }
    | .peek => {
        pre := fun s => s.count > 0
        post := fun s s' => s' = s
      }
    | .size => {
        pre := fun _ => True
        post := fun s s' => s' = s
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
        post := fun _ s' => s'.count = 0 ∧ s'.capacity = cap
      }
  inv := fun s => s.count ≤ s.capacity ∧ s.capacity = cap

/-! # Key Properties -/

/-- Write then read preserves count (net zero change). -/
theorem write_read_count {cap : Nat} {hcap : cap > 0}
    (s s1 s2 : RingBufState)
    (h_write : ((ringBufSpec cap hcap).opSpec .write).post s s1)
    (h_read : ((ringBufSpec cap hcap).opSpec .read).post s1 s2) :
    s2.count = s.count := by
  obtain ⟨h1, _⟩ := h_write
  obtain ⟨h2, _⟩ := h_read
  omega

/-- Clear sets count to zero. -/
theorem clear_empties {cap : Nat} {hcap : cap > 0}
    (s s' : RingBufState)
    (h_post : ((ringBufSpec cap hcap).opSpec .clear).post s s') :
    s'.count = 0 := by obtain ⟨h, _⟩ := h_post; exact h

/-- Invariant preserved by write. -/
theorem inv_write {cap : Nat} {hcap : cap > 0}
    (s s' : RingBufState)
    (h_inv : (ringBufSpec cap hcap).inv s)
    (_h_pre : ((ringBufSpec cap hcap).opSpec .write).pre s)
    (h_post : ((ringBufSpec cap hcap).opSpec .write).post s s') :
    (ringBufSpec cap hcap).inv s' := by
  obtain ⟨h_cnt, h_cap⟩ := h_inv
  obtain ⟨h1, h2⟩ := h_post
  exact ⟨by omega, by omega⟩

/-- Invariant preserved by read. -/
theorem inv_read {cap : Nat} {hcap : cap > 0}
    (s s' : RingBufState)
    (h_inv : (ringBufSpec cap hcap).inv s)
    (_h_pre : ((ringBufSpec cap hcap).opSpec .read).pre s)
    (h_post : ((ringBufSpec cap hcap).opSpec .read).post s s') :
    (ringBufSpec cap hcap).inv s' := by
  obtain ⟨h_cnt, h_cap⟩ := h_inv
  obtain ⟨h1, h2⟩ := h_post
  exact ⟨by omega, by omega⟩

/-- Invariant preserved by clear. -/
theorem inv_clear {cap : Nat} {hcap : cap > 0}
    (s s' : RingBufState)
    (_h_inv : (ringBufSpec cap hcap).inv s)
    (h_post : ((ringBufSpec cap hcap).opSpec .clear).post s s') :
    (ringBufSpec cap hcap).inv s' := by
  obtain ⟨h1, h2⟩ := h_post
  exact ⟨by omega, by omega⟩

/-! # Instantiation Guide

To verify a concrete C ring buffer (array-based, head/tail indices):

```
-- Simulation relation
def rbSim (cs : MyRB.ProgramState) (as : Specs.RingBuffer.RingBufState) : Prop :=
  -- Map C head/tail uint32_t to as.head/as.tail
  -- Map C count to as.count
  -- Map C capacity constant to as.capacity

-- Prove opRefinement for write, read, etc.
-- write_read_count guarantees net-zero count change.
-- For modular index arithmetic proofs, use Nat.mod_lt and omega.
```

For linked-list-based queues, use Specs.Queue instead.
-/

end Specs.RingBuffer
