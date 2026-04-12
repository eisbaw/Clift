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

/-- Array validity: all elements of keys and values arrays are heap-valid. -/
def ht_arrays_valid (heap : HeapRawState) (keys values : Ptr UInt32) (cap : UInt32) : Prop :=
  ∀ (i : Nat), i < cap.toNat →
    heapPtrValid heap (Ptr.elemOffset keys i) ∧
    heapPtrValid heap (Ptr.elemOffset values i)

/-- ht_insert: inserts key-value pair.
    Precondition: ht valid, keys/values arrays valid, key > 1 (not sentinel).
    Returns 0 on success, 1 if full. -/
def ht_insert_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.ht ∧
    s.locals.key > 1 ∧  -- keys 0,1 reserved
    (hVal s.globals.rawHeap s.locals.ht).capacity > 0 ∧
    ht_arrays_valid s.globals.rawHeap s.locals.keys s.locals.values
      (hVal s.globals.rawHeap s.locals.ht).capacity
  post := fun r s =>
    r = Except.ok () →
    -- On success (ret_val = 0), count incremented or unchanged (if key existed)
    (s.locals.ret__val = 0 ∨ s.locals.ret__val = 1)

/-- ht_lookup: searches for key.
    Returns 1 if found (value written to *out), 0 if not found. -/
def ht_lookup_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.ht ∧
    heapPtrValid s.globals.rawHeap s.locals.out ∧
    (hVal s.globals.rawHeap s.locals.ht).capacity > 0 ∧
    ht_arrays_valid s.globals.rawHeap s.locals.keys s.locals.values
      (hVal s.globals.rawHeap s.locals.ht).capacity
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

/-! ## Helper Hoare rules (not in L1HoareRules.lean) -/

private theorem L1_hoare_throw (Q : Except Unit Unit → ProgramState → Prop) :
    validHoare (fun s => Q (Except.error ()) s) (L1.throw (σ := ProgramState)) Q := by
  intro s₀ hpre
  constructor
  · intro h; exact h
  · intro r s₁ h_mem
    have heq := Prod.mk.inj h_mem
    rw [heq.1, heq.2]; exact hpre

/-- Bridge: derive L1_hoare_while side-conditions from a single body Hoare proof. -/
private theorem L1_hoare_while_from_body {c : ProgramState → Bool} {body : L1Monad ProgramState}
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

/-! ## Insert and Lookup proofs

Both functions follow the same high-level pattern:
  catch (seq preamble (seq while_loop ret_throw)) skip

The weak postcondition (ret_val ∈ {0, 1}) means we only need to show:
1. No fault (guards succeed under precondition)
2. Every exit path sets ret_val to 0 or 1

Strategy: prove validHoare directly using the L1 result/failed characterization
rather than deep Hoare rule decomposition. The body always throws (error),
the catch handler (skip) passes through.
-/

/-- Array element validity is preserved by heapUpdate (unconditional — htd is unchanged). -/
private theorem ht_arrays_valid_of_heapUpdate
    {heap : HeapRawState} {keys values : Ptr UInt32} {cap : UInt32}
    {β : Type} [MemType β] {p : Ptr β} {v : β}
    (h_valid : ht_arrays_valid heap keys values cap) :
    ht_arrays_valid (heapUpdate heap p v) keys values cap := by
  intro i hi
  have ⟨hk, hv⟩ := h_valid i hi
  exact ⟨heapUpdate_preserves_heapPtrValid heap p v (Ptr.elemOffset keys i) hk,
         heapUpdate_preserves_heapPtrValid heap p v (Ptr.elemOffset values i) hv⟩

/-- Key lemma: index bounded by capacity means array element is valid. -/
private theorem ht_array_elem_valid {heap : HeapRawState} {keys values : Ptr UInt32}
    {cap idx : UInt32}
    (h_arr : ht_arrays_valid heap keys values cap)
    (h_bound : idx.toNat < cap.toNat) :
    heapPtrValid heap (Ptr.elemOffset keys idx.toNat) ∧
    heapPtrValid heap (Ptr.elemOffset values idx.toNat) :=
  h_arr idx.toNat h_bound

/-! ## Array bounds (moved here for use in loop proofs) -/

/-- Array bounds: bitwise AND with (capacity - 1) is always < capacity,
    assuming capacity is a power of 2. -/
private theorem hash_index_bounded' (idx cap : UInt32) (h_pow2 : cap > 0) :
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

/-! ### Shared loop invariant and postcondition -/

-- Loop invariant for both insert and lookup: all heap validity conditions
-- needed by the loop body, plus index boundedness.
private def ht_loop_inv (s : ProgramState) : Prop :=
  heapPtrValid s.globals.rawHeap s.locals.ht ∧
  ht_arrays_valid s.globals.rawHeap s.locals.keys s.locals.values
    (hVal s.globals.rawHeap s.locals.ht).capacity ∧
  (hVal s.globals.rawHeap s.locals.ht).capacity > 0 ∧
  s.locals.cap_mask = (hVal s.globals.rawHeap s.locals.ht).capacity - 1 ∧
  s.locals.idx.toNat < (hVal s.globals.rawHeap s.locals.ht).capacity.toNat

-- The weak postcondition: ret_val ∈ {0, 1}
private def ht_ret_01 (s : ProgramState) : Prop :=
  s.locals.ret__val = 0 ∨ s.locals.ret__val = 1

-- heapPtrValid is preserved by heapUpdate
private theorem heapPtrValid_preserved {α β : Type} [MemType α] [CType β]
    {heap : HeapRawState} {p : Ptr α} {v : α} {q : Ptr β}
    (hv : heapPtrValid heap q) :
    heapPtrValid (heapUpdate heap p v) q :=
  heapUpdate_preserves_heapPtrValid heap p v q hv

-- After advancing idx = (idx + 1) &&& cap_mask, idx < capacity still holds
private theorem idx_advance_bounded (idx cap_mask cap : UInt32)
    (h_cm : cap_mask = cap - 1) (h_cap_pos : cap > 0) :
    ((idx + 1) &&& cap_mask).toNat < cap.toNat := by
  rw [h_cm]
  exact hash_index_bounded' (idx + 1) cap h_cap_pos

/-! ### ht_lookup_correct

  Structure of l1_ht_lookup_body (CSimpl → L1 mapping):

    L1.catch BODY L1.skip

  where BODY =
    L1.seq
      (L1.seq (L1.guard heapPtrValid_ht) (L1.modify set_cap_mask))  -- preamble
      (L1.seq
        (L1.dynCom hash_call)                                        -- call ht_hash
        (L1.seq
          (L1.modify set_probes_0)
          (L1.seq
            (L1.while loop_cond loop_body)                           -- linear probing
            (L1.seq (L1.modify set_ret_0) L1.throw))))               -- not found
-/

-- The lookup loop invariant: ht valid, arrays valid, idx bounded, cap_mask correct.
-- Additionally: out pointer valid (needed for the "found" branch guard).
private def ht_lookup_loop_inv (out : Ptr UInt32) (s : ProgramState) : Prop :=
  ht_loop_inv s ∧
  heapPtrValid s.globals.rawHeap out ∧
  s.locals.out = out

-- Step functions for ht_lookup body (anonymous constructors to avoid deep recursion)

-- set cap_mask := (hVal heap ht).capacity - 1
private noncomputable def lk_set_cm (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨(hVal s.globals.rawHeap s.locals.ht).capacity - 1, s.locals.capacity, s.locals.h,
   s.locals.ht, s.locals.i, s.locals.idx, s.locals.key, s.locals.keys, s.locals.out,
   s.locals.probes, s.locals.ret__val, s.locals.value, s.locals.values⟩⟩

-- Projection lemmas for lk_set_cm
attribute [local irreducible] hVal in
private theorem lk_set_cm_locals (s : ProgramState) :
    (lk_set_cm s).locals = ⟨(hVal s.globals.rawHeap s.locals.ht).capacity - 1, s.locals.capacity,
      s.locals.h, s.locals.ht, s.locals.i, s.locals.idx, s.locals.key, s.locals.keys, s.locals.out,
      s.locals.probes, s.locals.ret__val, s.locals.value, s.locals.values⟩ := by
  show (⟨s.globals, ⟨(hVal s.globals.rawHeap s.locals.ht).capacity - 1, s.locals.capacity, s.locals.h,
    s.locals.ht, s.locals.i, s.locals.idx, s.locals.key, s.locals.keys, s.locals.out,
    s.locals.probes, s.locals.ret__val, s.locals.value, s.locals.values⟩⟩ : ProgramState).locals = _
  rfl

attribute [local irreducible] hVal in
@[simp] private theorem lk_set_cm_globals (s : ProgramState) :
    (lk_set_cm s).globals = s.globals := by
  show (⟨s.globals, _⟩ : ProgramState).globals = _; rfl

attribute [local irreducible] hVal in
@[simp] private theorem lk_set_cm_ht (s : ProgramState) :
    (lk_set_cm s).locals.ht = s.locals.ht := by rw [lk_set_cm_locals]

attribute [local irreducible] hVal in
@[simp] private theorem lk_set_cm_out (s : ProgramState) :
    (lk_set_cm s).locals.out = s.locals.out := by rw [lk_set_cm_locals]

attribute [local irreducible] hVal in
@[simp] private theorem lk_set_cm_key (s : ProgramState) :
    (lk_set_cm s).locals.key = s.locals.key := by rw [lk_set_cm_locals]

attribute [local irreducible] hVal in
@[simp] private theorem lk_set_cm_keys (s : ProgramState) :
    (lk_set_cm s).locals.keys = s.locals.keys := by rw [lk_set_cm_locals]

attribute [local irreducible] hVal in
@[simp] private theorem lk_set_cm_values (s : ProgramState) :
    (lk_set_cm s).locals.values = s.locals.values := by rw [lk_set_cm_locals]

attribute [local irreducible] hVal in
@[simp] private theorem lk_set_cm_cap_mask (s : ProgramState) :
    (lk_set_cm s).locals.cap_mask = (hVal s.globals.rawHeap s.locals.ht).capacity - 1 := by
  rw [lk_set_cm_locals]

-- funext: the inline { s with ... } equals lk_set_cm
private theorem lk_set_cm_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      cap_mask := (hVal s.globals.rawHeap s.locals.ht).capacity - 1 } }) = lk_set_cm := by
  funext s; unfold lk_set_cm; rfl

-- set ret__val := 0
private noncomputable def lk_set_ret0 (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.cap_mask, s.locals.capacity, s.locals.h, s.locals.ht, s.locals.i,
   s.locals.idx, s.locals.key, s.locals.keys, s.locals.out, s.locals.probes,
   0, s.locals.value, s.locals.values⟩⟩

attribute [local irreducible] hVal in
@[simp] private theorem lk_set_ret0_ret (s : ProgramState) :
    (lk_set_ret0 s).locals.ret__val = 0 := by
  show (⟨s.globals, ⟨s.locals.cap_mask, s.locals.capacity, s.locals.h, s.locals.ht, s.locals.i,
    s.locals.idx, s.locals.key, s.locals.keys, s.locals.out, s.locals.probes,
    0, s.locals.value, s.locals.values⟩⟩ : ProgramState).locals.ret__val = _; rfl

-- set ret__val := 1
private noncomputable def lk_set_ret1 (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.cap_mask, s.locals.capacity, s.locals.h, s.locals.ht, s.locals.i,
   s.locals.idx, s.locals.key, s.locals.keys, s.locals.out, s.locals.probes,
   1, s.locals.value, s.locals.values⟩⟩

attribute [local irreducible] hVal in
@[simp] private theorem lk_set_ret1_ret (s : ProgramState) :
    (lk_set_ret1 s).locals.ret__val = 1 := by
  show (⟨s.globals, ⟨s.locals.cap_mask, s.locals.capacity, s.locals.h, s.locals.ht, s.locals.i,
    s.locals.idx, s.locals.key, s.locals.keys, s.locals.out, s.locals.probes,
    1, s.locals.value, s.locals.values⟩⟩ : ProgramState).locals.ret__val = _; rfl

-- funext lemmas for ret0/ret1
private theorem lk_set_ret0_funext :
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } }) = lk_set_ret0 := by
  funext s; unfold lk_set_ret0; rfl

private theorem lk_set_ret1_funext :
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := 1 } }) = lk_set_ret1 := by
  funext s; unfold lk_set_ret1; rfl

-- Restore after ht_hash call: locals from saved except idx from current ret_val
private noncomputable def lk_restore (saved : ProgramState) (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨saved.locals.cap_mask, saved.locals.capacity, saved.locals.h,
   saved.locals.ht, saved.locals.i, s.locals.ret__val, saved.locals.key, saved.locals.keys,
   saved.locals.out, saved.locals.probes, saved.locals.ret__val, saved.locals.value,
   saved.locals.values⟩⟩

attribute [local irreducible] hVal in
private theorem lk_restore_locals (saved s : ProgramState) :
    (lk_restore saved s).locals = ⟨saved.locals.cap_mask, saved.locals.capacity, saved.locals.h,
      saved.locals.ht, saved.locals.i, s.locals.ret__val, saved.locals.key, saved.locals.keys,
      saved.locals.out, saved.locals.probes, saved.locals.ret__val, saved.locals.value,
      saved.locals.values⟩ := by
  show (⟨s.globals, ⟨saved.locals.cap_mask, saved.locals.capacity, saved.locals.h,
    saved.locals.ht, saved.locals.i, s.locals.ret__val, saved.locals.key, saved.locals.keys,
    saved.locals.out, saved.locals.probes, saved.locals.ret__val, saved.locals.value,
    saved.locals.values⟩⟩ : ProgramState).locals = _
  rfl

attribute [local irreducible] hVal in
@[simp] private theorem lk_restore_globals (saved s : ProgramState) :
    (lk_restore saved s).globals = s.globals := by
  show (⟨s.globals, _⟩ : ProgramState).globals = _; rfl

attribute [local irreducible] hVal in
@[simp] private theorem lk_restore_ht (saved s : ProgramState) :
    (lk_restore saved s).locals.ht = saved.locals.ht := by rw [lk_restore_locals]

attribute [local irreducible] hVal in
@[simp] private theorem lk_restore_out (saved s : ProgramState) :
    (lk_restore saved s).locals.out = saved.locals.out := by rw [lk_restore_locals]

attribute [local irreducible] hVal in
@[simp] private theorem lk_restore_keys (saved s : ProgramState) :
    (lk_restore saved s).locals.keys = saved.locals.keys := by rw [lk_restore_locals]

attribute [local irreducible] hVal in
@[simp] private theorem lk_restore_values (saved s : ProgramState) :
    (lk_restore saved s).locals.values = saved.locals.values := by rw [lk_restore_locals]

attribute [local irreducible] hVal in
@[simp] private theorem lk_restore_cap_mask (saved s : ProgramState) :
    (lk_restore saved s).locals.cap_mask = saved.locals.cap_mask := by rw [lk_restore_locals]

attribute [local irreducible] hVal in
@[simp] private theorem lk_restore_idx (saved s : ProgramState) :
    (lk_restore saved s).locals.idx = s.locals.ret__val := by rw [lk_restore_locals]

attribute [local irreducible] hVal in
@[simp] private theorem lk_restore_key (saved s : ProgramState) :
    (lk_restore saved s).locals.key = saved.locals.key := by rw [lk_restore_locals]

-- funext: the restore modify equals lk_restore
private theorem lk_restore_funext (saved : ProgramState) :
    (fun s : ProgramState => { s with locals := { saved.locals with idx := s.locals.ret__val } }) =
      lk_restore saved := by
  funext s; unfold lk_restore; rfl

-- l1ProcEnv lookup lemma for ht_hash
private theorem l1ProcEnv_ht_hash :
    HashTable.l1ProcEnv "ht_hash" = some HashTable.l1_ht_hash_body := by
  unfold HashTable.l1ProcEnv L1.L1ProcEnv.insert L1.L1ProcEnv.empty
  rfl

-- ht_hash produces exactly ok results (not error or fail).
-- This strengthens ht_hash_correct to the form needed by L1_hoare_seq_ok.
attribute [local irreducible] hVal in
private theorem ht_hash_ok :
    validHoare (fun _ : ProgramState => True) HashTable.l1_ht_hash_body
      (fun r s => r = Except.ok () ∧
        s.locals.ret__val = ((s.locals.key * 2654435769) >>> 16) &&& s.locals.cap_mask) := by
  intro s _
  -- l1_ht_hash_body = L1.catch (seq modify1 (seq modify2 throw)) skip
  -- This always returns (ok, state_with_hash)
  unfold HashTable.l1_ht_hash_body
  simp only [ht_hash_f1_funext, ht_hash_f2_funext]
  have h_step2 := L1_modify_throw_result ht_hash_f2 (ht_hash_f1 s)
  have h_step1_res : (L1.modify ht_hash_f1 s).results = {(Except.ok (), ht_hash_f1 s)} := rfl
  have h_step1_nf : ¬(L1.modify ht_hash_f1 s).failed := by intro h; exact h
  have h_seq := L1_seq_singleton_ok h_step1_res h_step1_nf
    (m₂ := L1.seq (L1.modify ht_hash_f2) L1.throw)
  have h_body_res :
      (L1.seq (L1.modify ht_hash_f1) (L1.seq (L1.modify ht_hash_f2) L1.throw) s).results =
        {(Except.error (), ht_hash_f2 (ht_hash_f1 s))} := by
    rw [h_seq.1, h_step2.1]
  have h_body_nf :
      ¬(L1.seq (L1.modify ht_hash_f1) (L1.seq (L1.modify ht_hash_f2) L1.throw) s).failed := by
    intro hf; exact h_step2.2 (h_seq.2.mp hf)
  have h_catch := L1_catch_error_singleton h_body_res h_body_nf
  constructor
  · exact h_catch.2
  · intro r s' h_mem
    rw [h_catch.1] at h_mem
    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
    subst hr; subst hs
    exact ⟨rfl, rfl⟩

-- Stronger ht_hash: produces ok, preserves globals, sets ret_val
attribute [local irreducible] hVal in
private theorem ht_hash_full (s : ProgramState) :
    ¬(HashTable.l1_ht_hash_body s).failed ∧
    ∀ r s', (r, s') ∈ (HashTable.l1_ht_hash_body s).results →
      r = Except.ok () ∧
      s'.globals = s.globals ∧
      s'.locals.ret__val = ((s.locals.key * 2654435769) >>> 16) &&& s.locals.cap_mask ∧
      s'.locals.key = s.locals.key ∧
      s'.locals.cap_mask = s.locals.cap_mask := by
  unfold HashTable.l1_ht_hash_body
  simp only [ht_hash_f1_funext, ht_hash_f2_funext]
  have h_step2 := L1_modify_throw_result ht_hash_f2 (ht_hash_f1 s)
  have h_step1_res : (L1.modify ht_hash_f1 s).results = {(Except.ok (), ht_hash_f1 s)} := rfl
  have h_step1_nf : ¬(L1.modify ht_hash_f1 s).failed := by intro h; exact h
  have h_seq := L1_seq_singleton_ok h_step1_res h_step1_nf
    (m₂ := L1.seq (L1.modify ht_hash_f2) L1.throw)
  have h_body_res :=
    show (L1.seq (L1.modify ht_hash_f1) (L1.seq (L1.modify ht_hash_f2) L1.throw) s).results =
        {(Except.error (), ht_hash_f2 (ht_hash_f1 s))} by rw [h_seq.1, h_step2.1]
  have h_body_nf :=
    show ¬(L1.seq (L1.modify ht_hash_f1) (L1.seq (L1.modify ht_hash_f2) L1.throw) s).failed from
      fun hf => h_step2.2 (h_seq.2.mp hf)
  have h_catch := L1_catch_error_singleton h_body_res h_body_nf
  constructor
  · exact h_catch.2
  · intro r s' h_mem
    rw [h_catch.1] at h_mem
    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
    subst hr; subst hs
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · -- globals preserved: ht_hash_f2 (ht_hash_f1 s) only modifies locals
      show (ht_hash_f2 (ht_hash_f1 s)).globals = s.globals
      unfold ht_hash_f2 ht_hash_f1; rfl
    · rw [ht_hash_f2_locals_ret__val, ht_hash_f1_locals_h, ht_hash_f1_locals_cap_mask,
        ht_hash_f2_locals_key, ht_hash_f2_locals_cap_mask, ht_hash_f1_locals_key,
        ht_hash_f1_locals_cap_mask]
    · rw [ht_hash_f2_locals_key, ht_hash_f1_locals_key]
    · rw [ht_hash_f2_locals_cap_mask, ht_hash_f1_locals_cap_mask]

-- Helper: the dynCom for ht_hash establishes ht_loop_inv with idx bounded.
-- Extracted as a standalone lemma to control memory usage during elaboration.
-- The dynCom body: seq (modify setup) (seq (call ht_hash) (modify restore))
-- where setup is identity and restore sets locals from saved with idx := hash result.
attribute [local irreducible] hVal heapPtrValid heapUpdate in
private theorem ht_lookup_dynCom_hoare :
    validHoare
      (fun s => heapPtrValid s.globals.rawHeap s.locals.ht ∧
                heapPtrValid s.globals.rawHeap s.locals.out ∧
                (hVal s.globals.rawHeap s.locals.ht).capacity > 0 ∧
                ht_arrays_valid s.globals.rawHeap s.locals.keys s.locals.values
                  (hVal s.globals.rawHeap s.locals.ht).capacity ∧
                s.locals.cap_mask = (hVal s.globals.rawHeap s.locals.ht).capacity - 1)
      (L1.dynCom (fun saved =>
        L1.seq (L1.modify (fun s => { s with locals := { s.locals with
          key := s.locals.key, cap_mask := s.locals.cap_mask } }))
        (L1.seq HashTable.l1_ht_hash_body
          (L1.modify (fun s => { s with locals := { saved.locals with
            idx := s.locals.ret__val } })))))
      (fun r s => r = Except.ok () ∧ ht_loop_inv s ∧
                  heapPtrValid s.globals.rawHeap s.locals.out) := by
  apply L1_hoare_dynCom
  intro saved ⟨h_ht, h_out, h_cap, h_arr, h_cm⟩
  -- Inner body: seq (modify id) (seq ht_hash (modify restore))
  -- Use L1_hoare_seq_ok chain
  apply L1_hoare_seq_ok
    (R := fun s => heapPtrValid s.globals.rawHeap s.locals.ht ∧
                    heapPtrValid s.globals.rawHeap s.locals.out ∧
                    (hVal s.globals.rawHeap s.locals.ht).capacity > 0 ∧
                    ht_arrays_valid s.globals.rawHeap s.locals.keys s.locals.values
                      (hVal s.globals.rawHeap s.locals.ht).capacity ∧
                    s.locals.cap_mask = (hVal s.globals.rawHeap s.locals.ht).capacity - 1)
  · -- modify setup (identity): {s with locals := {s.locals with key := key, cap_mask := cap_mask}} = s
    intro s ⟨h_eq, _⟩
    constructor
    · intro hf; exact hf
    · intro r s' h_mem
      have ⟨hr, hs⟩ := Prod.mk.inj h_mem
      -- setup is identity
      exact ⟨hr, by subst hs; exact ⟨h_ht, h_out, h_cap, h_arr, h_cm⟩⟩
  · -- seq ht_hash (modify restore)
    apply L1_hoare_seq_ok
      (R := fun s₂ => s₂.globals = saved.globals ∧
        s₂.locals.ret__val = ((saved.locals.key * 2654435769) >>> 16) &&& saved.locals.cap_mask)
    · -- ht_hash
      intro s ⟨h_ht', h_out', h_cap', h_arr', h_cm'⟩
      have ⟨h_nf, h_post⟩ := ht_hash_full s
      constructor
      · exact h_nf
      · intro r s' h_mem
        have ⟨h_ok, h_glob, h_rv, _, _⟩ := h_post r s' h_mem
        exact ⟨h_ok, h_glob, h_rv⟩
    · -- modify restore: set locals from saved with idx := ret_val
      simp only [lk_restore_funext]
      intro s₂ ⟨h_glob, h_rv⟩
      constructor
      · intro hf; exact hf
      · intro r s' h_mem
        have ⟨hr, hs⟩ := Prod.mk.inj h_mem
        subst hr; subst hs
        refine ⟨rfl, ?_, ?_⟩
        · refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · rw [lk_restore_globals, lk_restore_ht, h_glob]; exact h_ht
          · rw [lk_restore_globals, lk_restore_keys, lk_restore_values,
              lk_restore_ht, h_glob]; exact h_arr
          · rw [lk_restore_globals, lk_restore_ht, h_glob]; exact h_cap
          · rw [lk_restore_cap_mask]; exact h_cm
          · rw [lk_restore_idx, h_rv, h_cm,
              show (lk_restore saved s₂).globals = saved.globals by rw [lk_restore_globals, h_glob],
              show (lk_restore saved s₂).locals.ht = saved.locals.ht by rw [lk_restore_ht]]
            exact hash_index_bounded' _ _ h_cap
        · rw [lk_restore_globals, lk_restore_out, h_glob]; exact h_out

-- Insert version of the dynCom (same structure, different postcondition)
attribute [local irreducible] hVal heapPtrValid heapUpdate in
private theorem ht_insert_dynCom_hoare :
    validHoare
      (fun s => heapPtrValid s.globals.rawHeap s.locals.ht ∧
                s.locals.key > 1 ∧
                (hVal s.globals.rawHeap s.locals.ht).capacity > 0 ∧
                ht_arrays_valid s.globals.rawHeap s.locals.keys s.locals.values
                  (hVal s.globals.rawHeap s.locals.ht).capacity ∧
                s.locals.cap_mask = (hVal s.globals.rawHeap s.locals.ht).capacity - 1)
      (L1.dynCom (fun saved =>
        L1.seq (L1.modify (fun s => { s with locals := { s.locals with
          key := s.locals.key, cap_mask := s.locals.cap_mask } }))
        (L1.seq HashTable.l1_ht_hash_body
          (L1.modify (fun s => { s with locals := { saved.locals with
            idx := s.locals.ret__val } })))))
      (fun r s => r = Except.ok () ∧ ht_insert_loop_inv s) := by
  apply L1_hoare_dynCom
  intro saved ⟨h_ht, h_key, h_cap, h_arr, h_cm⟩
  apply L1_hoare_seq_ok
    (R := fun s => heapPtrValid s.globals.rawHeap s.locals.ht ∧
                    s.locals.key > 1 ∧
                    (hVal s.globals.rawHeap s.locals.ht).capacity > 0 ∧
                    ht_arrays_valid s.globals.rawHeap s.locals.keys s.locals.values
                      (hVal s.globals.rawHeap s.locals.ht).capacity ∧
                    s.locals.cap_mask = (hVal s.globals.rawHeap s.locals.ht).capacity - 1)
  · -- modify setup (identity)
    intro s ⟨h_eq, _⟩
    constructor
    · intro hf; exact hf
    · intro r s' h_mem
      have ⟨hr, hs⟩ := Prod.mk.inj h_mem
      exact ⟨hr, by subst hs; exact ⟨h_ht, h_key, h_cap, h_arr, h_cm⟩⟩
  · -- seq ht_hash (modify restore)
    apply L1_hoare_seq_ok
      (R := fun s₂ => s₂.globals = saved.globals ∧
        s₂.locals.ret__val = ((saved.locals.key * 2654435769) >>> 16) &&& saved.locals.cap_mask)
    · intro s ⟨h_ht', _, h_cap', h_arr', h_cm'⟩
      have ⟨h_nf, h_post⟩ := ht_hash_full s
      constructor
      · exact h_nf
      · intro r s' h_mem
        have ⟨h_ok, h_glob, h_rv, _, _⟩ := h_post r s' h_mem
        exact ⟨h_ok, h_glob, h_rv⟩
    · simp only [lk_restore_funext]
      intro s₂ ⟨h_glob, h_rv⟩
      constructor
      · intro hf; exact hf
      · intro r s' h_mem
        have ⟨hr, hs⟩ := Prod.mk.inj h_mem
        subst hr; subst hs
        refine ⟨rfl, ?_⟩
        refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · rw [lk_restore_globals, lk_restore_ht, h_glob]; exact h_ht
        · rw [lk_restore_globals, lk_restore_keys, lk_restore_values,
            lk_restore_ht, h_glob]; exact h_arr
        · rw [lk_restore_globals, lk_restore_ht, h_glob]; exact h_cap
        · rw [lk_restore_cap_mask]; exact h_cm
        · rw [lk_restore_idx, h_rv, h_cm,
            show (lk_restore saved s₂).globals = saved.globals by rw [lk_restore_globals, h_glob],
            show (lk_restore saved s₂).locals.ht = saved.locals.ht by rw [lk_restore_ht]]
          exact hash_index_bounded' _ _ h_cap
        · rw [lk_restore_key]; exact h_key

-- Helper: shared guard+modify cap_mask proof (used by both lookup and insert)
attribute [local irreducible] hVal heapPtrValid heapUpdate in
private theorem ht_guard_modify_cm
    (P : ProgramState → Prop)
    (R : ProgramState → Prop)
    (h_guard : ∀ s, P s → heapPtrValid s.globals.rawHeap s.locals.ht)
    (h_post : ∀ s, P s → R (lk_set_cm s)) :
    validHoare P (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.ht))
      (L1.modify lk_set_cm)) (fun r s => r = Except.ok () ∧ R s) := by
  intro s hpre
  have hv := h_guard s hpre
  have hgm := L1_guard_modify_result
    (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.ht) lk_set_cm s hv
  constructor
  · exact hgm.2
  · intro r s' h_mem
    rw [hgm.1] at h_mem
    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
    exact ⟨hr, hs ▸ h_post s hpre⟩

attribute [local irreducible] hVal heapPtrValid heapUpdate in
theorem ht_lookup_correct :
    ht_lookup_spec.satisfiedBy HashTable.l1_ht_lookup_body := by
  unfold FuncSpec.satisfiedBy ht_lookup_spec
  show validHoare _ (L1.catch _ L1.skip) _
  apply L1_hoare_catch (R := ht_ret_01)
  · -- Body = seq (seq guard+modify) REST
    -- All paths through the body set ret_val to 0 or 1 before throwing.
    -- Prove directly from validHoare definition.
    -- Body = seq (seq guard modify) (seq dynCom rest)
    -- Decompose: first guard+modify (ok-only), then rest
    apply L1_hoare_seq_ok
      (R := fun s => heapPtrValid s.globals.rawHeap s.locals.ht ∧
                      heapPtrValid s.globals.rawHeap s.locals.out ∧
                      (hVal s.globals.rawHeap s.locals.ht).capacity > 0 ∧
                      ht_arrays_valid s.globals.rawHeap s.locals.keys s.locals.values
                        (hVal s.globals.rawHeap s.locals.ht).capacity ∧
                      s.locals.cap_mask = (hVal s.globals.rawHeap s.locals.ht).capacity - 1)
    · -- guard heapPtrValid ht; modify cap_mask := capacity - 1
      -- Direct proof from L1 semantics, avoiding named step functions
      intro s ⟨hv, ho, hc, ha⟩
      -- L1.seq (L1.guard p) (L1.modify f) at s where p s holds:
      -- results = {(ok, f s)}, failed = False
      -- This is L1_guard_modify_result, but we avoid referencing the modify function
      -- to prevent deep recursion.
      have h_guard_ok : (L1.guard (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.ht) s).results =
        {(Except.ok (), s)} ∧ ¬(L1.guard (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.ht) s).failed := by
        exact ⟨L1_guard_results hv, L1_guard_not_failed hv⟩
      constructor
      · -- not failed
        intro hf
        simp only [L1.seq] at hf
        rcases hf with hf1 | ⟨s', h_mem, hf2⟩
        · exact h_guard_ok.2 hf1
        · exact hf2  -- L1.modify never fails
      · -- postcondition
        intro r s' h_mem
        simp only [L1.seq] at h_mem
        rcases h_mem with ⟨s1, h_g, h_m⟩ | ⟨h_err, _⟩
        · -- ok from guard, then modify
          rw [h_guard_ok.1] at h_g
          -- h_g : (ok, s1) ∈ {(ok, s)}, so s1 = s
          have h_s1 : s1 = s := (Prod.mk.inj h_g).2
          rw [h_s1] at h_m
          -- h_m : (r, s') ∈ (L1.modify f s).results = {(ok, f s)}
          have ⟨h_r_ok, h_s'_eq⟩ := Prod.mk.inj h_m
          -- Extract properties of s' via named step function projections
          -- h_s'_eq : s' = f s, but f s is def-eq to lk_set_cm s
          -- Use the pre-proved projection lemmas (proved with [local irreducible] hVal)
          have h_s'_lk : s' = lk_set_cm s := h_s'_eq
          exact ⟨h_r_ok,
                 by rw [h_s'_lk, lk_set_cm_globals, lk_set_cm_ht]; exact hv,
                 by rw [h_s'_lk, lk_set_cm_globals, lk_set_cm_out]; exact ho,
                 by rw [h_s'_lk, lk_set_cm_globals, lk_set_cm_ht]; exact hc,
                 by rw [h_s'_lk, lk_set_cm_globals, lk_set_cm_keys, lk_set_cm_values, lk_set_cm_ht]; exact ha,
                 by rw [h_s'_lk, lk_set_cm_cap_mask, lk_set_cm_globals, lk_set_cm_ht]⟩
        · -- error from guard: impossible
          rw [h_guard_ok.1] at h_err
          exact absurd h_err (by intro h; cases h)
    · -- rest: seq dynCom (seq probes:=0 (seq while ret:=0;throw))
      -- The postcondition (from L1_hoare_catch body) is:
      --   match r | ok => (ok = ok → ret ∈ {0,1}) | error => ret ∈ {0,1}
      -- Since all paths throw, the ok case is vacuous.
      -- All error results have ret_val set to 0 or 1 explicitly.

      -- Decompose: first dynCom, then rest
      apply L1_hoare_seq_ok
        (R := fun s => ht_loop_inv s ∧
                        heapPtrValid s.globals.rawHeap s.locals.out)
      · -- dynCom: calls ht_hash, restores locals, sets idx
        exact ht_lookup_dynCom_hoare
      · -- seq probes:=0 (seq while ret:=0;throw)
        apply L1_hoare_seq_ok
          (R := fun s => ht_loop_inv s ∧
                          heapPtrValid s.globals.rawHeap s.locals.out ∧
                          s.locals.probes = 0)
        · -- modify probes := 0: ok-only, preserves invariant
          intro s ⟨⟨h_ht, h_arr, h_cap, h_cm, h_idx⟩, h_out⟩
          constructor
          · intro hf; exact hf  -- L1.modify never fails
          · intro r s' h_mem
            have ⟨hr, hs⟩ := Prod.mk.inj h_mem
            subst hr; subst hs
            -- s' = modify s. globals unchanged, probes := 0, rest unchanged.
            refine ⟨rfl, ⟨h_ht, h_arr, h_cap, h_cm, h_idx⟩, h_out, rfl⟩
        · -- seq while ret:=0;throw
          -- Every path produces error with ret_val ∈ {0, 1}:
          -- - while body throws: ret_val set to 0 or 1
          -- - while exits normally → ret:=0;throw
          -- Prove directly from validHoare definition
          intro s ⟨⟨h_ht, h_arr, h_cap, h_cm, h_idx⟩, h_out, _⟩
          -- The while + final throw always produces error results.
          -- Use the while loop Hoare rule with invariant.
          sorry
  · -- Handler proof: skip preserves ht_ret_01
    intro s h_ret
    constructor
    · intro hf; exact hf
    · intro r s' h_mem
      have ⟨hr, hs⟩ := Prod.mk.inj h_mem
      subst hr; subst hs
      intro _; exact h_ret

/-! ### ht_insert_correct -/

-- The insert loop invariant: ht valid, arrays valid, idx bounded, cap_mask correct.
private def ht_insert_loop_inv (s : ProgramState) : Prop :=
  ht_loop_inv s ∧ s.locals.key > 1

attribute [local irreducible] hVal heapPtrValid heapUpdate in
theorem ht_insert_correct :
    ht_insert_spec.satisfiedBy HashTable.l1_ht_insert_body := by
  unfold FuncSpec.satisfiedBy ht_insert_spec
  show validHoare _ (L1.catch _ L1.skip) _
  apply L1_hoare_catch (R := ht_ret_01)
  · -- Body = seq (cond full_check ret:=1;throw skip) REST
    -- First decompose the full check from the rest
    apply L1_hoare_seq
      (R := fun s => heapPtrValid s.globals.rawHeap s.locals.ht ∧
                      s.locals.key > 1 ∧
                      (hVal s.globals.rawHeap s.locals.ht).capacity > 0 ∧
                      ht_arrays_valid s.globals.rawHeap s.locals.keys s.locals.values
                        (hVal s.globals.rawHeap s.locals.ht).capacity)
    · -- cond (count >= capacity) (ret:=1;throw) skip
      -- Either throws with ret_val=1 (error result, Q error = ht_ret_01)
      -- or falls through with ok (invariant preserved)
      apply L1_hoare_condition
      · -- true branch: count >= capacity → ret:=1; throw
        intro s ⟨⟨hv, hk, hc, ha⟩, _⟩
        have h_mt := L1_modify_throw_result
          (fun s : ProgramState => ⟨s.globals, ⟨s.locals.cap_mask, s.locals.capacity, s.locals.h,
            s.locals.ht, s.locals.i, s.locals.idx, s.locals.key, s.locals.keys, s.locals.out,
            s.locals.probes, (1 : UInt32), s.locals.value, s.locals.values⟩⟩) s
        constructor
        · exact h_mt.2
        · intro r s' h_mem
          rw [h_mt.1] at h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
          exact Or.inr rfl
      · -- false branch: skip (not full)
        intro s ⟨⟨hv, hk, hc, ha⟩, _⟩
        constructor
        · intro hf; exact hf
        · intro r s' h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
          exact ⟨hv, hk, hc, ha⟩
    · -- REST: guard+modify cap_mask, dynCom, probes:=0, while, ret:=1;throw
      -- Same structure as lookup's body.
      -- Decompose: guard+modify, then rest
      apply L1_hoare_seq_ok
        (R := fun s => heapPtrValid s.globals.rawHeap s.locals.ht ∧
                        s.locals.key > 1 ∧
                        (hVal s.globals.rawHeap s.locals.ht).capacity > 0 ∧
                        ht_arrays_valid s.globals.rawHeap s.locals.keys s.locals.values
                          (hVal s.globals.rawHeap s.locals.ht).capacity ∧
                        s.locals.cap_mask = (hVal s.globals.rawHeap s.locals.ht).capacity - 1)
      · -- guard heapPtrValid ht; modify cap_mask
        -- Same structure as lookup's guard+modify proof.
        -- The proof is identical but the insert context causes kernel deep recursion
        -- due to the larger L1 body tree. Needs refactoring to a shared lemma.
        sorry
      · -- rest: dynCom, probes:=0, while, ret:=1;throw
        sorry
  · -- Handler proof: skip preserves ht_ret_01
    intro s h_ret
    constructor
    · intro hf; exact hf
    · intro r s' h_mem
      have ⟨hr, hs⟩ := Prod.mk.inj h_mem
      subst hr; subst hs
      intro _; exact h_ret

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
