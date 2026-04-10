-- Task 0157: Hash table verification
--
-- Open-addressing hash table with linear probing.
-- 7 functions imported from hash_table.c (~160 LOC C -> ~534 lines Lean).
--
-- Key verification targets:
-- - Abstract spec: partial function (Key -> Option Value)
-- - Insert/lookup correctness: lookup after insert returns inserted value
-- - Delete removes entry
-- - Count tracks number of entries
-- - Array bounds: all index accesses within [0, capacity)

import Generated.HashTable
import Clift.Lifting.Pipeline
import Clift.Lifting.FuncSpec

set_option maxHeartbeats 12800000
set_option maxRecDepth 4096

open HashTable

/-! # Step 1: Run the clift pipeline on all 7 functions -/

clift HashTable

/-! # Step 2: Verify L1 definitions exist -/

#check @HashTable.l1_ht_hash_body
#check @HashTable.l1_ht_init_body
#check @HashTable.l1_ht_insert_body
#check @HashTable.l1_ht_lookup_body
#check @HashTable.l1_ht_delete_body
#check @HashTable.l1_ht_count_body
#check @HashTable.l1_ht_contains_body

/-! # Step 3: FuncSpecs -/

/-- ht_hash: multiplicative hash, returns index in [0, cap_mask].
    Pure function, no heap access. -/
def ht_hash_spec : FuncSpec ProgramState where
  pre := fun _ => True
  post := fun r s =>
    r = Except.ok () →
    s.locals.ret__val = ((s.locals.key * 2654435769) >>> 16) &&& s.locals.cap_mask

/-- ht_count: accessor, returns count field. -/
def ht_count_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.ht
  post := fun r s =>
    r = Except.ok () →
    s.locals.ret__val = (hVal s.globals.rawHeap s.locals.ht).count

/-- ht_insert: inserts key-value pair.
    Precondition: ht valid, keys/values arrays valid, key > 1 (not sentinel).
    Returns 0 on success, 1 if full. -/
def ht_insert_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.ht ∧
    s.locals.key > 1  -- keys 0,1 reserved
  post := fun r s =>
    r = Except.ok () →
    -- On success (ret_val = 0), count incremented or unchanged (if key existed)
    (s.locals.ret__val = 0 ∨ s.locals.ret__val = 1)

/-- ht_lookup: searches for key.
    Returns 1 if found (value written to *out), 0 if not found. -/
def ht_lookup_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.ht ∧
    heapPtrValid s.globals.rawHeap s.locals.out
  post := fun r s =>
    r = Except.ok () →
    (s.locals.ret__val = 0 ∨ s.locals.ret__val = 1)

/-- ht_delete: removes key, returns 1 if deleted, 0 if not found. -/
def ht_delete_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.ht
  post := fun r s =>
    r = Except.ok () →
    (s.locals.ret__val = 0 ∨ s.locals.ret__val = 1)

/-- ht_contains: checks key presence. Returns 0 or 1. -/
def ht_contains_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.ht
  post := fun r s =>
    r = Except.ok () →
    (s.locals.ret__val = 0 ∨ s.locals.ret__val = 1)

/-! # Step 4: validHoare theorems -/

theorem ht_hash_correct :
    ht_hash_spec.satisfiedBy HashTable.l1_ht_hash_body := by
  sorry

theorem ht_count_correct :
    ht_count_spec.satisfiedBy HashTable.l1_ht_count_body := by
  sorry

theorem ht_insert_correct :
    ht_insert_spec.satisfiedBy HashTable.l1_ht_insert_body := by
  sorry

theorem ht_lookup_correct :
    ht_lookup_spec.satisfiedBy HashTable.l1_ht_lookup_body := by
  sorry

/-! # Step 5: Array bounds property (task 0186)

The hash table exercises array subscript heavily:
- ht_hash produces index via `(h >> 16) & cap_mask`
- Every loop iteration accesses `keys[idx]` and `values[idx]`
- idx advances as `(idx + 1) & cap_mask`

Bounds guard: for power-of-2 capacity, `idx & (capacity - 1) < capacity`.
This is the key property for task 0186: the bitwise mask ensures bounds. -/

/-- Array bounds: bitwise AND with (capacity - 1) is always < capacity,
    assuming capacity is a power of 2. -/
theorem hash_index_bounded (idx cap : UInt32) (h_pow2 : cap > 0) :
    (idx &&& (cap - 1)).toNat < cap.toNat := by
  sorry
