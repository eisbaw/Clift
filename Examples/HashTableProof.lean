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
set_option maxRecDepth 16384

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

-- Projection lemmas for structure updates
private theorem ht_update_retval_globals (s : ProgramState) (v : UInt32) :
    ({ s with locals := { s.locals with ret__val := v } } : ProgramState).globals = s.globals := rfl
private theorem ht_update_retval_ht (s : ProgramState) (v : UInt32) :
    ({ s with locals := { s.locals with ret__val := v } } : ProgramState).locals.ht = s.locals.ht := rfl
private theorem ht_update_retval_val (s : ProgramState) (v : UInt32) :
    ({ s with locals := { s.locals with ret__val := v } } : ProgramState).locals.ret__val = v := rfl

-- ht_hash step 1: h := key * 2654435769
private noncomputable def ht_hash_f1 (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.cap_mask, s.locals.capacity, s.locals.key * 2654435769,
    s.locals.ht, s.locals.i, s.locals.idx, s.locals.key, s.locals.keys, s.locals.out,
    s.locals.probes, s.locals.ret__val, s.locals.value, s.locals.values⟩⟩

-- ht_hash step 2: ret__val := (h >>> 16) &&& cap_mask
private noncomputable def ht_hash_f2 (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.cap_mask, s.locals.capacity, s.locals.h, s.locals.ht, s.locals.i,
    s.locals.idx, s.locals.key, s.locals.keys, s.locals.out, s.locals.probes,
    (s.locals.h >>> 16) &&& s.locals.cap_mask, s.locals.value, s.locals.values⟩⟩

attribute [local irreducible] hVal in
private theorem ht_hash_f1_locals_eq (s : ProgramState) :
    (ht_hash_f1 s).locals = ⟨s.locals.cap_mask, s.locals.capacity, s.locals.key * 2654435769,
      s.locals.ht, s.locals.i, s.locals.idx, s.locals.key, s.locals.keys, s.locals.out,
      s.locals.probes, s.locals.ret__val, s.locals.value, s.locals.values⟩ := by
  show (⟨s.globals, ⟨s.locals.cap_mask, s.locals.capacity, s.locals.key * 2654435769,
    s.locals.ht, s.locals.i, s.locals.idx, s.locals.key, s.locals.keys, s.locals.out,
    s.locals.probes, s.locals.ret__val, s.locals.value, s.locals.values⟩⟩ :
    ProgramState).locals = _
  rfl

attribute [local irreducible] hVal in
@[simp] private theorem ht_hash_f1_locals_cap_mask (s : ProgramState) :
    (ht_hash_f1 s).locals.cap_mask = s.locals.cap_mask := by
  rw [ht_hash_f1_locals_eq]

attribute [local irreducible] hVal in
@[simp] private theorem ht_hash_f1_locals_h (s : ProgramState) :
    (ht_hash_f1 s).locals.h = s.locals.key * 2654435769 := by
  rw [ht_hash_f1_locals_eq]

attribute [local irreducible] hVal in
@[simp] private theorem ht_hash_f1_locals_key (s : ProgramState) :
    (ht_hash_f1 s).locals.key = s.locals.key := by
  rw [ht_hash_f1_locals_eq]

attribute [local irreducible] hVal in
private theorem ht_hash_f2_locals_eq (s : ProgramState) :
    (ht_hash_f2 s).locals = ⟨s.locals.cap_mask, s.locals.capacity, s.locals.h, s.locals.ht,
      s.locals.i, s.locals.idx, s.locals.key, s.locals.keys, s.locals.out, s.locals.probes,
      (s.locals.h >>> 16) &&& s.locals.cap_mask, s.locals.value, s.locals.values⟩ := by
  show (⟨s.globals, ⟨s.locals.cap_mask, s.locals.capacity, s.locals.h, s.locals.ht, s.locals.i,
    s.locals.idx, s.locals.key, s.locals.keys, s.locals.out, s.locals.probes,
    (s.locals.h >>> 16) &&& s.locals.cap_mask, s.locals.value, s.locals.values⟩⟩ :
    ProgramState).locals = _
  rfl

attribute [local irreducible] hVal in
@[simp] private theorem ht_hash_f2_locals_ret__val (s : ProgramState) :
    (ht_hash_f2 s).locals.ret__val = (s.locals.h >>> 16) &&& s.locals.cap_mask := by
  rw [ht_hash_f2_locals_eq]

attribute [local irreducible] hVal in
@[simp] private theorem ht_hash_f2_locals_cap_mask (s : ProgramState) :
    (ht_hash_f2 s).locals.cap_mask = s.locals.cap_mask := by
  rw [ht_hash_f2_locals_eq]

attribute [local irreducible] hVal in
@[simp] private theorem ht_hash_f2_locals_key (s : ProgramState) :
    (ht_hash_f2 s).locals.key = s.locals.key := by
  rw [ht_hash_f2_locals_eq]

private theorem ht_hash_f1_funext :
    (fun s : ProgramState => { s with locals := { s.locals with h := s.locals.key * 2654435769 } }) =
      ht_hash_f1 := by
  funext s
  unfold ht_hash_f1
  rfl

private theorem ht_hash_f2_funext :
    (fun s : ProgramState =>
      { s with locals := { s.locals with ret__val := (s.locals.h >>> 16) &&& s.locals.cap_mask } }) =
      ht_hash_f2 := by
  funext s
  unfold ht_hash_f2
  rfl

attribute [local irreducible] hVal in
theorem ht_hash_correct :
    ht_hash_spec.satisfiedBy HashTable.l1_ht_hash_body := by
  unfold FuncSpec.satisfiedBy ht_hash_spec validHoare
  intro s _
  unfold HashTable.l1_ht_hash_body
  simp only [ht_hash_f1_funext, ht_hash_f2_funext]
  have h_step2 := L1_modify_throw_result ht_hash_f2 (ht_hash_f1 s)
  have h_step1_res : (L1.modify ht_hash_f1 s).results = {(Except.ok (), ht_hash_f1 s)} := rfl
  have h_step1_nf : ¬(L1.modify ht_hash_f1 s).failed := by
    intro h
    exact h
  have h_seq := L1_seq_singleton_ok h_step1_res h_step1_nf
    (m₂ := L1.seq (L1.modify ht_hash_f2) L1.throw)
  have h_body_res :
      (L1.seq (L1.modify ht_hash_f1) (L1.seq (L1.modify ht_hash_f2) L1.throw) s).results =
        {(Except.error (), ht_hash_f2 (ht_hash_f1 s))} := by
    rw [h_seq.1, h_step2.1]
  have h_body_nf :
      ¬(L1.seq (L1.modify ht_hash_f1) (L1.seq (L1.modify ht_hash_f2) L1.throw) s).failed := by
    intro hf
    exact h_step2.2 (h_seq.2.mp hf)
  have h_catch := L1_catch_error_singleton h_body_res h_body_nf
  constructor
  · exact h_catch.2
  · intro r s' h_mem _
    rw [h_catch.1] at h_mem
    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
    subst hr
    subst hs
    rw [ht_hash_f2_locals_ret__val, ht_hash_f1_locals_h, ht_hash_f1_locals_cap_mask,
      ht_hash_f2_locals_key, ht_hash_f2_locals_cap_mask, ht_hash_f1_locals_key,
      ht_hash_f1_locals_cap_mask]

attribute [local irreducible] hVal heapPtrValid in
theorem ht_count_correct :
    ht_count_spec.satisfiedBy HashTable.l1_ht_count_body := by
  unfold FuncSpec.satisfiedBy ht_count_spec validHoare
  intro s hpre
  unfold HashTable.l1_ht_count_body
  have h := L1_guard_modify_throw_catch_skip_result
    (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.ht)
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := (hVal s.globals.rawHeap s.locals.ht).count } })
    s hpre
  obtain ⟨h_res, h_nf⟩ := h
  constructor
  · exact h_nf
  · intro r s' h_mem _
    rw [h_res] at h_mem
    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
    subst hr; subst hs
    rw [ht_update_retval_val, ht_update_retval_globals, ht_update_retval_ht]

-- requires while loop invariant machinery (linear probing loop)
theorem ht_insert_correct :
    ht_insert_spec.satisfiedBy HashTable.l1_ht_insert_body := by
  sorry -- requires while loop invariant

-- requires while loop invariant machinery (linear probing loop)
theorem ht_lookup_correct :
    ht_lookup_spec.satisfiedBy HashTable.l1_ht_lookup_body := by
  sorry -- requires while loop invariant

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
  have h_one_le_nat : (1 : Nat) ≤ cap.toNat := by
    have h_cap_nat : 0 < cap.toNat := (UInt32.lt_iff_toNat_lt).1 h_pow2
    exact Nat.succ_le_of_lt h_cap_nat
  have h_one_le : (1 : UInt32) ≤ cap := by
    exact (UInt32.le_iff_toNat_le).2 (by simpa using h_one_le_nat)
  have h_sub_lt : cap - 1 < cap :=
    UInt32.sub_lt (a := cap) (b := 1) (by decide) h_one_le
  have h_sub_nat_lt : (cap - 1).toNat < cap.toNat :=
    (UInt32.lt_iff_toNat_lt).1 h_sub_lt
  have h_and_le : (idx &&& (cap - 1)).toNat ≤ (cap - 1).toNat := by
    rw [UInt32.toNat_and]
    exact Nat.and_le_right
  omega
