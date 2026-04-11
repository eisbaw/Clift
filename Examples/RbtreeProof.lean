-- Task 0159: Red-black tree verification
--
-- BST with arena-based node storage (parallel arrays).
-- 7 functions imported from rbtree.c (~200 LOC C -> ~833 lines Lean).
--
-- Key verification targets:
-- - BST property: left < node < right
-- - Lookup correctness: find after insert returns inserted value
-- - Rotation preserves BST property
-- - Count tracks number of nodes

import Generated.Rbtree
import Clift.Lifting.Pipeline
import Clift.Lifting.FuncSpec

set_option maxHeartbeats 12800000
set_option maxRecDepth 4096

open Rbtree

/-! # Step 1: Run the clift pipeline on all 7 functions -/

clift Rbtree

/-! # Step 2: Verify L1 definitions exist -/

#check @Rbtree.l1_rbt_init_body
#check @Rbtree.l1_rbt_lookup_body
#check @Rbtree.l1_rbt_rotate_left_body
#check @Rbtree.l1_rbt_rotate_right_body
#check @Rbtree.l1_rbt_insert_bst_body
#check @Rbtree.l1_rbt_count_body
#check @Rbtree.l1_rbt_min_body

/-! # Step 3: BST property as abstract spec -/

/-- Abstract BST: a set of (key, value) pairs with ordering. -/
inductive BST where
  | leaf : BST
  | node : BST → Nat → Nat → BST → BST  -- left, key, value, right
  deriving Repr

/-- BST ordering invariant: all keys in left < key < all keys in right. -/
def BST.ordered : BST → Prop
  | .leaf => True
  | .node l k _ r =>
    (∀ k', BST.mem k' l → k' < k) ∧
    (∀ k', BST.mem k' r → k < k') ∧
    l.ordered ∧ r.ordered
where
  BST.mem (k : Nat) : BST → Prop
    | .leaf => False
    | .node l k' _ r => k = k' ∨ BST.mem k l ∨ BST.mem k r

/-- Lookup in the abstract BST. -/
def BST.lookup (key : Nat) : BST → Option Nat
  | .leaf => none
  | .node l k v r =>
    if key = k then some v
    else if key < k then BST.lookup key l
    else BST.lookup key r

/-- Insert into the abstract BST (no balancing). -/
def BST.insert (key value : Nat) : BST → BST
  | .leaf => .node .leaf key value .leaf
  | .node l k v r =>
    if key = k then .node l k value r
    else if key < k then .node (BST.insert key value l) k v r
    else .node l k v (BST.insert key value r)

/-- Key property: lookup after insert returns the inserted value. -/
theorem BST.lookup_insert (t : BST) (k v : Nat) (h_ord : t.ordered) :
    BST.lookup k (BST.insert k v t) = some v := by
  induction t with
  | leaf => simp [BST.insert, BST.lookup]
  | node l k' v' r ih_l ih_r =>
    unfold BST.insert
    by_cases h_eq : k = k'
    · -- k = k': replace value, lookup trivially finds it
      simp [h_eq, BST.lookup]
    · by_cases h_lt : k < k'
      · -- k < k': insert into left, lookup into left
        simp only [h_eq, ite_false, h_lt, ite_true, BST.lookup]
        exact ih_l h_ord.2.2.1
      · -- k > k': insert into right, lookup into right
        simp only [h_eq, ite_false, h_lt, BST.lookup]
        exact ih_r h_ord.2.2.2

/-! # Step 4: FuncSpecs -/

/-- rbt_count: accessor. -/
def rbt_count_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.t
  post := fun r s =>
    r = Except.ok () →
    s.locals.ret__val = (hVal s.globals.rawHeap s.locals.t).count

/-- All nodes reachable from `idx` in the parallel-array BST have valid array entries.
    Arena-based analog of LinkedListValid. -/
inductive RbtNodeValid (heap : HeapRawState)
    (keys vals lefts rights : Ptr UInt32) : UInt32 → Prop where
  | null : RbtNodeValid heap keys vals lefts rights 4294967295
  | node (idx : UInt32) (h_ne : idx ≠ 4294967295)
         (h_keys : heapPtrValid heap (Ptr.elemOffset keys idx.toNat))
         (h_vals : heapPtrValid heap (Ptr.elemOffset vals idx.toNat))
         (h_lefts : heapPtrValid heap (Ptr.elemOffset lefts idx.toNat))
         (h_rights : heapPtrValid heap (Ptr.elemOffset rights idx.toNat))
         (h_left : RbtNodeValid heap keys vals lefts rights
                     (hVal heap (Ptr.elemOffset lefts idx.toNat)))
         (h_right : RbtNodeValid heap keys vals lefts rights
                      (hVal heap (Ptr.elemOffset rights idx.toNat))) :
    RbtNodeValid heap keys vals lefts rights idx

theorem RbtNodeValid.keys_valid {heap keys vals lefts rights idx}
    (h : RbtNodeValid heap keys vals lefts rights idx) (h_ne : idx ≠ 4294967295) :
    heapPtrValid heap (Ptr.elemOffset keys idx.toNat) := by
  cases h with | null => exact absurd rfl h_ne | node _ _ hk _ _ _ _ _ => exact hk

theorem RbtNodeValid.vals_valid {heap keys vals lefts rights idx}
    (h : RbtNodeValid heap keys vals lefts rights idx) (h_ne : idx ≠ 4294967295) :
    heapPtrValid heap (Ptr.elemOffset vals idx.toNat) := by
  cases h with | null => exact absurd rfl h_ne | node _ _ _ hv _ _ _ _ => exact hv

theorem RbtNodeValid.lefts_valid {heap keys vals lefts rights idx}
    (h : RbtNodeValid heap keys vals lefts rights idx) (h_ne : idx ≠ 4294967295) :
    heapPtrValid heap (Ptr.elemOffset lefts idx.toNat) := by
  cases h with | null => exact absurd rfl h_ne | node _ _ _ _ hl _ _ _ => exact hl

theorem RbtNodeValid.rights_valid {heap keys vals lefts rights idx}
    (h : RbtNodeValid heap keys vals lefts rights idx) (h_ne : idx ≠ 4294967295) :
    heapPtrValid heap (Ptr.elemOffset rights idx.toNat) := by
  cases h with | null => exact absurd rfl h_ne | node _ _ _ _ _ hr _ _ => exact hr

theorem RbtNodeValid.left_child {heap keys vals lefts rights idx}
    (h : RbtNodeValid heap keys vals lefts rights idx) (h_ne : idx ≠ 4294967295) :
    RbtNodeValid heap keys vals lefts rights
      (hVal heap (Ptr.elemOffset lefts idx.toNat)) := by
  cases h with | null => exact absurd rfl h_ne | node _ _ _ _ _ _ hl _ => exact hl

theorem RbtNodeValid.right_child {heap keys vals lefts rights idx}
    (h : RbtNodeValid heap keys vals lefts rights idx) (h_ne : idx ≠ 4294967295) :
    RbtNodeValid heap keys vals lefts rights
      (hVal heap (Ptr.elemOffset rights idx.toNat)) := by
  cases h with | null => exact absurd rfl h_ne | node _ _ _ _ _ _ _ hr => exact hr

/-- heapUpdate at a disjoint pointer preserves RbtNodeValid.
    Since lookup only writes to `found` (a UInt32 scalar), and the tree arrays are
    Ptr UInt32 arrays at different addresses, we need this for the abrupt-exit case. -/
theorem RbtNodeValid.of_heapUpdate_found {heap : HeapRawState}
    {keys vals lefts rights : Ptr UInt32} {found : Ptr UInt32} {v : UInt32} {idx : UInt32}
    (h : RbtNodeValid heap keys vals lefts rights idx)
    (h_bound_f : found.addr.val + CType.size UInt32 ≤ memSize)
    (h_disj_keys : ∀ i, ptrDisjoint found (Ptr.elemOffset keys i))
    (h_disj_vals : ∀ i, ptrDisjoint found (Ptr.elemOffset vals i))
    (h_disj_lefts : ∀ i, ptrDisjoint found (Ptr.elemOffset lefts i))
    (h_disj_rights : ∀ i, ptrDisjoint found (Ptr.elemOffset rights i)) :
    RbtNodeValid (heapUpdate heap found v) keys vals lefts rights idx := by
  induction h with
  | null => exact .null
  | node idx h_ne hk hv hl hr h_left h_right ih_l ih_r =>
    have hk' := heapUpdate_preserves_heapPtrValid heap found v _ hk
    have hv' := heapUpdate_preserves_heapPtrValid heap found v _ hv
    have hl' := heapUpdate_preserves_heapPtrValid heap found v _ hl
    have hr' := heapUpdate_preserves_heapPtrValid heap found v _ hr
    have h_bl := heapPtrValid_bound hl
    have h_br := heapPtrValid_bound hr
    have h_left_eq := hVal_heapUpdate_disjoint heap found (Ptr.elemOffset lefts idx.toNat) v h_bound_f h_bl (h_disj_lefts _)
    have h_right_eq := hVal_heapUpdate_disjoint heap found (Ptr.elemOffset rights idx.toNat) v h_bound_f h_br (h_disj_rights _)
    refine .node idx h_ne hk' hv' hl' hr' ?_ ?_
    · rw [h_left_eq]; exact ih_l
    · rw [h_right_eq]; exact ih_r

/-- rbt_lookup: BST search. Returns value if found, sets *found.
    Precondition strengthened to include arena validity for reachable nodes. -/
def rbt_lookup_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.t ∧
    heapPtrValid s.globals.rawHeap s.locals.found ∧
    RbtNodeValid s.globals.rawHeap s.locals.keys s.locals.vals
      s.locals.lefts s.locals.rights
      (hVal s.globals.rawHeap s.locals.t).root ∧
    -- found pointer is disjoint from all array element pointers
    (∀ i, ptrDisjoint s.locals.found (Ptr.elemOffset s.locals.keys i)) ∧
    (∀ i, ptrDisjoint s.locals.found (Ptr.elemOffset s.locals.vals i)) ∧
    (∀ i, ptrDisjoint s.locals.found (Ptr.elemOffset s.locals.lefts i)) ∧
    (∀ i, ptrDisjoint s.locals.found (Ptr.elemOffset s.locals.rights i))
  post := fun r s =>
    r = Except.ok () →
    -- found is set to 0 or 1
    let found_val := hVal s.globals.rawHeap s.locals.found
    (found_val = 0 ∨ found_val = 1)

/-- rbt_init: initializes empty tree. -/
def rbt_init_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.t
  post := fun r s =>
    r = Except.ok () →
    let t := hVal s.globals.rawHeap s.locals.t
    t.root = 0xFFFFFFFF ∧
    t.count = 0 ∧
    t.next_free = 0

/-! # Step 5: validHoare theorems -/

private theorem rb_retval_globals (s : ProgramState) (v : UInt32) :
    ({ s with locals := { s.locals with ret__val := v } } : ProgramState).globals = s.globals := rfl
private theorem rb_retval_t (s : ProgramState) (v : UInt32) :
    ({ s with locals := { s.locals with ret__val := v } } : ProgramState).locals.t = s.locals.t := rfl
private theorem rb_retval_val (s : ProgramState) (v : UInt32) :
    ({ s with locals := { s.locals with ret__val := v } } : ProgramState).locals.ret__val = v := rfl

attribute [local irreducible] hVal heapPtrValid in
theorem rbt_count_correct :
    rbt_count_spec.satisfiedBy Rbtree.l1_rbt_count_body := by
  unfold FuncSpec.satisfiedBy rbt_count_spec validHoare
  intro s hpre
  unfold Rbtree.l1_rbt_count_body
  have h := L1_guard_modify_throw_catch_skip_result
    (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.t)
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := (hVal s.globals.rawHeap s.locals.t).count } })
    s hpre
  obtain ⟨h_res, h_nf⟩ := h
  constructor
  · exact h_nf
  · intro r s' h_mem _
    rw [h_res] at h_mem
    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
    subst hr; subst hs
    rw [rb_retval_val, rb_retval_globals, rb_retval_t]

/-! ## rbt_init: direct result computation using L1 result lemmas. -/

-- Helper: heapUpdate preserves heapPtrValid at same pointer for C_rbtree
private theorem rbt_heapUpdate_t_ptrValid (s : ProgramState)
    (hv : heapPtrValid s.globals.rawHeap s.locals.t)
    (v : C_rbtree) :
    heapPtrValid (heapUpdate s.globals.rawHeap s.locals.t v) s.locals.t :=
  heapUpdate_preserves_heapPtrValid _ _ _ _ hv

theorem rbt_init_correct :
    rbt_init_spec.satisfiedBy Rbtree.l1_rbt_init_body := by
  unfold FuncSpec.satisfiedBy rbt_init_spec validHoare
  intro s hpre
  -- Define the 4 modify functions and intermediate states inline
  let p := fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.t
  let f1 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.t ({ hVal s.globals.rawHeap s.locals.t with root := 4294967295 } : C_rbtree) } }
  let f2 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.t ({ hVal s.globals.rawHeap s.locals.t with count := 0 } : C_rbtree) } }
  let f3 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.t ({ hVal s.globals.rawHeap s.locals.t with next_free := 0 } : C_rbtree) } }
  let f4 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.t ({ hVal s.globals.rawHeap s.locals.t with capacity := s.locals.capacity } : C_rbtree) } }
  let s1 := f1 s
  let s2 := f2 s1
  let s3 := f3 s2
  let s4 := f4 s3
  -- heapPtrValid preservation
  have hv1 : p s1 := rbt_heapUpdate_t_ptrValid s hpre _
  have hv2 : p s2 := rbt_heapUpdate_t_ptrValid s1 hv1 _
  have hv3 : p s3 := rbt_heapUpdate_t_ptrValid s2 hv2 _
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
  unfold Rbtree.l1_rbt_init_body
  constructor
  · exact h_catch.2
  · intro r s' h_mem
    rw [h_catch.1] at h_mem
    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
    subst hr; subst hs
    intro _
    -- Chain hVal_heapUpdate_same at each step
    have hb := heapPtrValid_bound hpre
    have hb1 := heapPtrValid_bound hv1
    have hb2 := heapPtrValid_bound hv2
    have hb3 := heapPtrValid_bound hv3
    have h4v : hVal s4.globals.rawHeap s4.locals.t =
        ({ hVal s3.globals.rawHeap s3.locals.t with capacity := s3.locals.capacity } : C_rbtree) :=
      hVal_heapUpdate_same _ _ _ hb3
    have h3v : hVal s3.globals.rawHeap s3.locals.t =
        ({ hVal s2.globals.rawHeap s2.locals.t with next_free := 0 } : C_rbtree) :=
      hVal_heapUpdate_same _ _ _ hb2
    have h2v : hVal s2.globals.rawHeap s2.locals.t =
        ({ hVal s1.globals.rawHeap s1.locals.t with count := 0 } : C_rbtree) :=
      hVal_heapUpdate_same _ _ _ hb1
    have h1v : hVal s1.globals.rawHeap s1.locals.t =
        ({ hVal s.globals.rawHeap s.locals.t with root := 4294967295 } : C_rbtree) :=
      hVal_heapUpdate_same _ _ _ hb
    rw [h4v, h3v, h2v, h1v]
    exact ⟨rfl, rfl, rfl⟩

-- Convenience: FoundOk for the postcondition
private def FoundOk (s : ProgramState) : Prop :=
  hVal s.globals.rawHeap s.locals.found = 0 ∨
  hVal s.globals.rawHeap s.locals.found = 1

-- The loop invariant for rbt_lookup's while loop
private def rbt_lookup_inv (s : ProgramState) : Prop :=
  heapPtrValid s.globals.rawHeap s.locals.found ∧
  hVal s.globals.rawHeap s.locals.found = 0 ∧
  RbtNodeValid s.globals.rawHeap s.locals.keys s.locals.vals
    s.locals.lefts s.locals.rights s.locals.curr ∧
  (∀ i, ptrDisjoint s.locals.found (Ptr.elemOffset s.locals.keys i)) ∧
  (∀ i, ptrDisjoint s.locals.found (Ptr.elemOffset s.locals.vals i)) ∧
  (∀ i, ptrDisjoint s.locals.found (Ptr.elemOffset s.locals.lefts i)) ∧
  (∀ i, ptrDisjoint s.locals.found (Ptr.elemOffset s.locals.rights i))

-- Bridge: derive L1_hoare_while conditions from a single validHoare on the body
private theorem L1_hoare_while_from_body {σ : Type} {c : σ → Bool} {body : L1Monad σ}
    {I : σ → Prop} {Q : Except Unit Unit → σ → Prop}
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

-- L1_hoare_throw: not in L1HoareRules.lean, add locally
private theorem L1_hoare_throw {σ : Type} (Q : Except Unit Unit → σ → Prop) :
    validHoare (fun s => Q (Except.error ()) s) (L1.throw (σ := σ)) Q := by
  intro s₀ hpre
  constructor
  · intro h; exact h
  · intro r s₁ h_mem
    have heq := Prod.mk.inj h_mem
    rw [heq.1, heq.2]; exact hpre

/-! ## Anonymous constructor helper functions -/

private noncomputable def rbt_go_left (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.capacity, s.locals.colors,
   hVal s.globals.rawHeap (Ptr.elemOffset s.locals.lefts s.locals.curr.toNat),
   s.locals.found, s.locals.key, s.locals.keys, s.locals.lefts,
   s.locals.new_node, s.locals.par, s.locals.parents, s.locals.ret__val,
   s.locals.rights, s.locals.t, s.locals.vals, s.locals.value,
   s.locals.x, s.locals.xp, s.locals.y, s.locals.yp⟩⟩

private noncomputable def rbt_go_right (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.capacity, s.locals.colors,
   hVal s.globals.rawHeap (Ptr.elemOffset s.locals.rights s.locals.curr.toNat),
   s.locals.found, s.locals.key, s.locals.keys, s.locals.lefts,
   s.locals.new_node, s.locals.par, s.locals.parents, s.locals.ret__val,
   s.locals.rights, s.locals.t, s.locals.vals, s.locals.value,
   s.locals.x, s.locals.xp, s.locals.y, s.locals.yp⟩⟩

private noncomputable def rbt_set_found1 (s : ProgramState) : ProgramState :=
  ⟨⟨heapUpdate s.globals.rawHeap s.locals.found 1⟩, s.locals⟩

private noncomputable def rbt_set_retval_curr (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.capacity, s.locals.colors, s.locals.curr,
   s.locals.found, s.locals.key, s.locals.keys, s.locals.lefts,
   s.locals.new_node, s.locals.par, s.locals.parents,
   hVal s.globals.rawHeap (Ptr.elemOffset s.locals.vals s.locals.curr.toNat),
   s.locals.rights, s.locals.t, s.locals.vals, s.locals.value,
   s.locals.x, s.locals.xp, s.locals.y, s.locals.yp⟩⟩

private noncomputable def rbt_set_curr_root (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.capacity, s.locals.colors,
   (hVal s.globals.rawHeap s.locals.t).root,
   s.locals.found, s.locals.key, s.locals.keys, s.locals.lefts,
   s.locals.new_node, s.locals.par, s.locals.parents, s.locals.ret__val,
   s.locals.rights, s.locals.t, s.locals.vals, s.locals.value,
   s.locals.x, s.locals.xp, s.locals.y, s.locals.yp⟩⟩

private noncomputable def rbt_init_found0 (s : ProgramState) : ProgramState :=
  ⟨⟨heapUpdate s.globals.rawHeap s.locals.found 0⟩, s.locals⟩

private noncomputable def rbt_set_retval0 (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.capacity, s.locals.colors, s.locals.curr,
   s.locals.found, s.locals.key, s.locals.keys, s.locals.lefts,
   s.locals.new_node, s.locals.par, s.locals.parents, (0 : UInt32),
   s.locals.rights, s.locals.t, s.locals.vals, s.locals.value,
   s.locals.x, s.locals.xp, s.locals.y, s.locals.yp⟩⟩

/-! ## Projection lemmas (two-step pattern)

The kernel cannot reduce (⟨g, ⟨f1,...,f19⟩⟩ : CState Locals).locals.fi
in one step due to its depth limit. We split into:
  Step 1: .locals = ⟨f1,...,f19⟩  (one iota on CState.mk)
  Step 2: rw to get .fi from the known Locals constructor (shallow iota)

For .globals (first field of CState), direct unfold+rfl works. -/

-- rbt_go_left: ⟨s.globals, ⟨..., new_curr, ...⟩⟩
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_go_left_globals (s : ProgramState) :
    (rbt_go_left s).globals = s.globals := by unfold rbt_go_left; rfl
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_go_left_locals_eq (s : ProgramState) :
    (rbt_go_left s).locals = ⟨s.locals.capacity, s.locals.colors,
      hVal s.globals.rawHeap (Ptr.elemOffset s.locals.lefts s.locals.curr.toNat),
      s.locals.found, s.locals.key, s.locals.keys, s.locals.lefts,
      s.locals.new_node, s.locals.par, s.locals.parents, s.locals.ret__val,
      s.locals.rights, s.locals.t, s.locals.vals, s.locals.value,
      s.locals.x, s.locals.xp, s.locals.y, s.locals.yp⟩ := by unfold rbt_go_left; rfl
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_go_left_locals_found (s : ProgramState) :
    (rbt_go_left s).locals.found = s.locals.found := by rw [rbt_go_left_locals_eq]
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_go_left_locals_keys (s : ProgramState) :
    (rbt_go_left s).locals.keys = s.locals.keys := by rw [rbt_go_left_locals_eq]
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_go_left_locals_vals (s : ProgramState) :
    (rbt_go_left s).locals.vals = s.locals.vals := by rw [rbt_go_left_locals_eq]
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_go_left_locals_lefts (s : ProgramState) :
    (rbt_go_left s).locals.lefts = s.locals.lefts := by rw [rbt_go_left_locals_eq]
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_go_left_locals_rights (s : ProgramState) :
    (rbt_go_left s).locals.rights = s.locals.rights := by rw [rbt_go_left_locals_eq]
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_go_left_locals_curr (s : ProgramState) :
    (rbt_go_left s).locals.curr =
      hVal s.globals.rawHeap (Ptr.elemOffset s.locals.lefts s.locals.curr.toNat) := by
  rw [rbt_go_left_locals_eq]

-- rbt_go_right: ⟨s.globals, ⟨..., new_curr, ...⟩⟩
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_go_right_globals (s : ProgramState) :
    (rbt_go_right s).globals = s.globals := by unfold rbt_go_right; rfl
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_go_right_locals_eq (s : ProgramState) :
    (rbt_go_right s).locals = ⟨s.locals.capacity, s.locals.colors,
      hVal s.globals.rawHeap (Ptr.elemOffset s.locals.rights s.locals.curr.toNat),
      s.locals.found, s.locals.key, s.locals.keys, s.locals.lefts,
      s.locals.new_node, s.locals.par, s.locals.parents, s.locals.ret__val,
      s.locals.rights, s.locals.t, s.locals.vals, s.locals.value,
      s.locals.x, s.locals.xp, s.locals.y, s.locals.yp⟩ := by unfold rbt_go_right; rfl
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_go_right_locals_found (s : ProgramState) :
    (rbt_go_right s).locals.found = s.locals.found := by rw [rbt_go_right_locals_eq]
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_go_right_locals_keys (s : ProgramState) :
    (rbt_go_right s).locals.keys = s.locals.keys := by rw [rbt_go_right_locals_eq]
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_go_right_locals_vals (s : ProgramState) :
    (rbt_go_right s).locals.vals = s.locals.vals := by rw [rbt_go_right_locals_eq]
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_go_right_locals_lefts (s : ProgramState) :
    (rbt_go_right s).locals.lefts = s.locals.lefts := by rw [rbt_go_right_locals_eq]
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_go_right_locals_rights (s : ProgramState) :
    (rbt_go_right s).locals.rights = s.locals.rights := by rw [rbt_go_right_locals_eq]
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_go_right_locals_curr (s : ProgramState) :
    (rbt_go_right s).locals.curr =
      hVal s.globals.rawHeap (Ptr.elemOffset s.locals.rights s.locals.curr.toNat) := by
  rw [rbt_go_right_locals_eq]

-- rbt_set_found1: ⟨⟨heapUpdate ...⟩, s.locals⟩ — locals unchanged
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_set_found1_locals (s : ProgramState) :
    (rbt_set_found1 s).locals = s.locals := by unfold rbt_set_found1; rfl
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_set_found1_globals_rawHeap (s : ProgramState) :
    (rbt_set_found1 s).globals.rawHeap =
      heapUpdate s.globals.rawHeap s.locals.found 1 := by
  show (⟨heapUpdate s.globals.rawHeap s.locals.found 1⟩ : Globals).rawHeap = _
  rfl

-- rbt_set_retval_curr: ⟨s.globals, ⟨..., new_retval, ...⟩⟩
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_set_retval_curr_globals (s : ProgramState) :
    (rbt_set_retval_curr s).globals = s.globals := by unfold rbt_set_retval_curr; rfl
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_set_retval_curr_locals_eq (s : ProgramState) :
    (rbt_set_retval_curr s).locals = ⟨s.locals.capacity, s.locals.colors, s.locals.curr,
      s.locals.found, s.locals.key, s.locals.keys, s.locals.lefts,
      s.locals.new_node, s.locals.par, s.locals.parents,
      hVal s.globals.rawHeap (Ptr.elemOffset s.locals.vals s.locals.curr.toNat),
      s.locals.rights, s.locals.t, s.locals.vals, s.locals.value,
      s.locals.x, s.locals.xp, s.locals.y, s.locals.yp⟩ := by
  unfold rbt_set_retval_curr; rfl
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_set_retval_curr_locals_found (s : ProgramState) :
    (rbt_set_retval_curr s).locals.found = s.locals.found := by
  rw [rbt_set_retval_curr_locals_eq]

-- rbt_set_curr_root: ⟨s.globals, ⟨..., new_curr, ...⟩⟩
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_set_curr_root_globals (s : ProgramState) :
    (rbt_set_curr_root s).globals = s.globals := by unfold rbt_set_curr_root; rfl
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_set_curr_root_locals_eq (s : ProgramState) :
    (rbt_set_curr_root s).locals = ⟨s.locals.capacity, s.locals.colors,
      (hVal s.globals.rawHeap s.locals.t).root,
      s.locals.found, s.locals.key, s.locals.keys, s.locals.lefts,
      s.locals.new_node, s.locals.par, s.locals.parents, s.locals.ret__val,
      s.locals.rights, s.locals.t, s.locals.vals, s.locals.value,
      s.locals.x, s.locals.xp, s.locals.y, s.locals.yp⟩ := by unfold rbt_set_curr_root; rfl
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_set_curr_root_locals_found (s : ProgramState) :
    (rbt_set_curr_root s).locals.found = s.locals.found := by rw [rbt_set_curr_root_locals_eq]
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_set_curr_root_locals_keys (s : ProgramState) :
    (rbt_set_curr_root s).locals.keys = s.locals.keys := by rw [rbt_set_curr_root_locals_eq]
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_set_curr_root_locals_vals (s : ProgramState) :
    (rbt_set_curr_root s).locals.vals = s.locals.vals := by rw [rbt_set_curr_root_locals_eq]
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_set_curr_root_locals_lefts (s : ProgramState) :
    (rbt_set_curr_root s).locals.lefts = s.locals.lefts := by rw [rbt_set_curr_root_locals_eq]
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_set_curr_root_locals_rights (s : ProgramState) :
    (rbt_set_curr_root s).locals.rights = s.locals.rights := by rw [rbt_set_curr_root_locals_eq]
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_set_curr_root_locals_curr (s : ProgramState) :
    (rbt_set_curr_root s).locals.curr =
      (hVal s.globals.rawHeap s.locals.t).root := by rw [rbt_set_curr_root_locals_eq]

-- rbt_init_found0: ⟨⟨heapUpdate ...⟩, s.locals⟩ — locals unchanged
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_init_found0_locals (s : ProgramState) :
    (rbt_init_found0 s).locals = s.locals := by unfold rbt_init_found0; rfl
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_init_found0_globals_rawHeap (s : ProgramState) :
    (rbt_init_found0 s).globals.rawHeap =
      heapUpdate s.globals.rawHeap s.locals.found 0 := by
  show (⟨heapUpdate s.globals.rawHeap s.locals.found 0⟩ : Globals).rawHeap = _
  rfl

-- rbt_set_retval0: ⟨s.globals, ⟨..., 0, ...⟩⟩
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_set_retval0_globals (s : ProgramState) :
    (rbt_set_retval0 s).globals = s.globals := by unfold rbt_set_retval0; rfl
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_set_retval0_locals_eq (s : ProgramState) :
    (rbt_set_retval0 s).locals = ⟨s.locals.capacity, s.locals.colors, s.locals.curr,
      s.locals.found, s.locals.key, s.locals.keys, s.locals.lefts,
      s.locals.new_node, s.locals.par, s.locals.parents, (0 : UInt32),
      s.locals.rights, s.locals.t, s.locals.vals, s.locals.value,
      s.locals.x, s.locals.xp, s.locals.y, s.locals.yp⟩ := by unfold rbt_set_retval0; rfl
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_set_retval0_locals_found (s : ProgramState) :
    (rbt_set_retval0 s).locals.found = s.locals.found := by rw [rbt_set_retval0_locals_eq]

/-! ## Invariant preservation and FoundOk lemmas -/

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_go_left_preserves_inv (s : ProgramState)
    (h_inv : rbt_lookup_inv s) (h_ne : s.locals.curr ≠ 4294967295) :
    rbt_lookup_inv (rbt_go_left s) := by
  obtain ⟨h_fv, h_f0, h_valid, h_dk, h_dv, h_dl, h_dr⟩ := h_inv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rbt_go_left_globals, rbt_go_left_locals_found]; exact h_fv
  · rw [rbt_go_left_globals, rbt_go_left_locals_found]; exact h_f0
  · rw [rbt_go_left_globals, rbt_go_left_locals_keys, rbt_go_left_locals_vals,
        rbt_go_left_locals_lefts, rbt_go_left_locals_rights, rbt_go_left_locals_curr]
    exact h_valid.left_child h_ne
  · intro i; rw [rbt_go_left_locals_found, rbt_go_left_locals_keys]; exact h_dk i
  · intro i; rw [rbt_go_left_locals_found, rbt_go_left_locals_vals]; exact h_dv i
  · intro i; rw [rbt_go_left_locals_found, rbt_go_left_locals_lefts]; exact h_dl i
  · intro i; rw [rbt_go_left_locals_found, rbt_go_left_locals_rights]; exact h_dr i

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_go_right_preserves_inv (s : ProgramState)
    (h_inv : rbt_lookup_inv s) (h_ne : s.locals.curr ≠ 4294967295) :
    rbt_lookup_inv (rbt_go_right s) := by
  obtain ⟨h_fv, h_f0, h_valid, h_dk, h_dv, h_dl, h_dr⟩ := h_inv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rbt_go_right_globals, rbt_go_right_locals_found]; exact h_fv
  · rw [rbt_go_right_globals, rbt_go_right_locals_found]; exact h_f0
  · rw [rbt_go_right_globals, rbt_go_right_locals_keys, rbt_go_right_locals_vals,
        rbt_go_right_locals_lefts, rbt_go_right_locals_rights, rbt_go_right_locals_curr]
    exact h_valid.right_child h_ne
  · intro i; rw [rbt_go_right_locals_found, rbt_go_right_locals_keys]; exact h_dk i
  · intro i; rw [rbt_go_right_locals_found, rbt_go_right_locals_vals]; exact h_dv i
  · intro i; rw [rbt_go_right_locals_found, rbt_go_right_locals_lefts]; exact h_dl i
  · intro i; rw [rbt_go_right_locals_found, rbt_go_right_locals_rights]; exact h_dr i

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_found_branch_foundok (s : ProgramState)
    (h_fv : heapPtrValid s.globals.rawHeap s.locals.found) :
    FoundOk (rbt_set_retval_curr (rbt_set_found1 s)) := by
  unfold FoundOk; right
  rw [rbt_set_retval_curr_globals, rbt_set_retval_curr_locals_found,
      rbt_set_found1_globals_rawHeap, rbt_set_found1_locals]
  exact hVal_heapUpdate_same _ _ _ (heapPtrValid_bound h_fv)

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_teardown_foundok (s : ProgramState)
    (h_f0 : hVal s.globals.rawHeap s.locals.found = 0) :
    FoundOk (rbt_set_retval0 s) := by
  unfold FoundOk; left
  rw [rbt_set_retval0_globals, rbt_set_retval0_locals_found]; exact h_f0

/-! ## Function extensionality: {s with ...} = anonymous constructor

These are needed to rewrite the generated L1 body's modify functions
to our anonymous constructor forms. -/

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_set_curr_root_funext :
    (fun s : ProgramState => { s with locals := { s.locals with curr :=
        (hVal s.globals.rawHeap s.locals.t).root } }) = rbt_set_curr_root := by
  funext s; unfold rbt_set_curr_root; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_init_found0_funext :
    (fun s : ProgramState =>
      { s with globals := { s.globals with rawHeap :=
        (heapUpdate s.globals.rawHeap s.locals.found 0) } }) = rbt_init_found0 := by
  funext s; unfold rbt_init_found0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_set_found1_funext :
    (fun s : ProgramState =>
      { s with globals := { s.globals with rawHeap :=
        (heapUpdate s.globals.rawHeap s.locals.found 1) } }) = rbt_set_found1 := by
  funext s; unfold rbt_set_found1; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_set_retval_curr_funext :
    (fun s : ProgramState =>
      { s with locals := { s.locals with ret__val :=
        (hVal s.globals.rawHeap (Ptr.elemOffset s.locals.vals s.locals.curr.toNat)) } }) =
    rbt_set_retval_curr := by
  funext s; unfold rbt_set_retval_curr; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_go_left_funext :
    (fun s : ProgramState =>
      { s with locals := { s.locals with curr :=
        (hVal s.globals.rawHeap (Ptr.elemOffset s.locals.lefts s.locals.curr.toNat)) } }) =
    rbt_go_left := by
  funext s; unfold rbt_go_left; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_go_right_funext :
    (fun s : ProgramState =>
      { s with locals := { s.locals with curr :=
        (hVal s.globals.rawHeap (Ptr.elemOffset s.locals.rights s.locals.curr.toNat)) } }) =
    rbt_go_right := by
  funext s; unfold rbt_go_right; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rbt_set_retval0_funext :
    (fun s : ProgramState =>
      { s with locals := { s.locals with ret__val := (0 : UInt32) } }) =
    rbt_set_retval0 := by
  funext s; unfold rbt_set_retval0; rfl

/-! ## Main correctness theorem -/

set_option maxRecDepth 8192 in
set_option maxHeartbeats 25600000 in
attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem rbt_lookup_correct :
    rbt_lookup_spec.satisfiedBy Rbtree.l1_rbt_lookup_body := by
  show validHoare rbt_lookup_spec.pre Rbtree.l1_rbt_lookup_body rbt_lookup_spec.post
  unfold Rbtree.l1_rbt_lookup_body
  simp only [rbt_set_curr_root_funext, rbt_init_found0_funext, rbt_set_found1_funext,
             rbt_set_retval_curr_funext, rbt_go_left_funext, rbt_go_right_funext,
             rbt_set_retval0_funext]
  apply L1_hoare_catch (R := FoundOk)
  · apply L1_hoare_seq
      (R := fun s =>
        heapPtrValid s.globals.rawHeap s.locals.found ∧
        RbtNodeValid s.globals.rawHeap s.locals.keys s.locals.vals
          s.locals.lefts s.locals.rights s.locals.curr ∧
        (∀ i, ptrDisjoint s.locals.found (Ptr.elemOffset s.locals.keys i)) ∧
        (∀ i, ptrDisjoint s.locals.found (Ptr.elemOffset s.locals.vals i)) ∧
        (∀ i, ptrDisjoint s.locals.found (Ptr.elemOffset s.locals.lefts i)) ∧
        (∀ i, ptrDisjoint s.locals.found (Ptr.elemOffset s.locals.rights i)))
    · -- Setup: guard ptrValid t >> modify rbt_set_curr_root
      intro s hpre
      unfold rbt_lookup_spec at hpre
      obtain ⟨h_tv, h_fv, h_tree, h_dk, h_dv, h_dl, h_dr⟩ := hpre
      have h_gm := L1_guard_modify_result
        (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.t)
        rbt_set_curr_root s h_tv
      constructor
      · exact h_gm.2
      · intro r s' h_mem
        rw [h_gm.1] at h_mem
        have ⟨hr, hs⟩ := Prod.mk.inj h_mem
        subst hr; subst hs
        rw [rbt_set_curr_root_globals, rbt_set_curr_root_locals_found,
            rbt_set_curr_root_locals_keys, rbt_set_curr_root_locals_vals,
            rbt_set_curr_root_locals_lefts, rbt_set_curr_root_locals_rights,
            rbt_set_curr_root_locals_curr]
        exact ⟨h_fv, h_tree, h_dk, h_dv, h_dl, h_dr⟩
    · -- Rest: seq init_found (seq while teardown)
      apply L1_hoare_seq (R := rbt_lookup_inv)
      · -- init_found: guard ptrValid found >> modify rbt_init_found0
        intro s ⟨h_fv, h_tree, h_dk, h_dv, h_dl, h_dr⟩
        have h_gm := L1_guard_modify_result
          (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.found)
          rbt_init_found0 s h_fv
        constructor
        · exact h_gm.2
        · intro r s' h_mem
          rw [h_gm.1] at h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem
          subst hr; subst hs
          unfold rbt_lookup_inv
          rw [rbt_init_found0_locals, rbt_init_found0_globals_rawHeap]
          refine ⟨heapUpdate_preserves_heapPtrValid _ _ _ _ h_fv,
                  hVal_heapUpdate_same _ _ _ (heapPtrValid_bound h_fv),
                  ?_, h_dk, h_dv, h_dl, h_dr⟩
          exact RbtNodeValid.of_heapUpdate_found h_tree
            (heapPtrValid_bound h_fv) h_dk h_dv h_dl h_dr
      · -- seq while teardown
        apply L1_hoare_seq (R := fun s => rbt_lookup_inv s)
        · -- While loop
          apply L1_hoare_while_from_body
          · -- body Hoare
            apply L1_hoare_seq
              (P := fun s => rbt_lookup_inv s ∧ (decide (s.locals.curr ≠ 4294967295)) = true)
              (R := fun s => rbt_lookup_inv s ∧ (decide (s.locals.curr ≠ 4294967295)) = true)
            · -- First condition: found or skip
              apply L1_hoare_condition
              · -- key = keys[curr]: found branch
                intro s ⟨⟨h_inv, h_cond⟩, h_key_eq⟩
                have h_ne : s.locals.curr ≠ 4294967295 := by
                  simp at h_cond; exact h_cond
                obtain ⟨h_fv, h_f0, h_valid, h_dk, h_dv, h_dl, h_dr⟩ := h_inv
                have h_gm1 := L1_guard_modify_result
                  (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.found)
                  rbt_set_found1 s h_fv
                have h_vv := h_valid.vals_valid h_ne
                have h_vv1 : heapPtrValid (rbt_set_found1 s).globals.rawHeap
                    (Ptr.elemOffset (rbt_set_found1 s).locals.vals (rbt_set_found1 s).locals.curr.toNat) :=
                  (rbt_set_found1_globals_rawHeap s).symm ▸ (rbt_set_found1_locals s).symm ▸
                    heapUpdate_preserves_heapPtrValid _ _ _ _ h_vv
                have h_mt := L1_modify_throw_result rbt_set_retval_curr (rbt_set_found1 s)
                -- guard+rest at (rbt_set_found1 s): use guard_modify result lemmas
                -- The guard predicate p applied to (rbt_set_found1 s) reduces to h_vv1's type
                have h_guard_res := L1_guard_results (p := fun s => heapPtrValid s.globals.rawHeap
                    (Ptr.elemOffset s.locals.vals s.locals.curr.toNat)) (s := rbt_set_found1 s) h_vv1
                have h_guard_nf := L1_guard_not_failed (p := fun s => heapPtrValid s.globals.rawHeap
                    (Ptr.elemOffset s.locals.vals s.locals.curr.toNat)) (s := rbt_set_found1 s) h_vv1
                have h_seq2 := L1_seq_singleton_ok h_guard_res h_guard_nf
                  (m₂ := L1.seq (L1.modify rbt_set_retval_curr) L1.throw)
                have h_inner2_res :
                    (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap
                        (Ptr.elemOffset s.locals.vals s.locals.curr.toNat)))
                      (L1.seq (L1.modify rbt_set_retval_curr) L1.throw) (rbt_set_found1 s)).results =
                    {(Except.error (), rbt_set_retval_curr (rbt_set_found1 s))} := by
                  rw [h_seq2.1, h_mt.1]
                have h_inner2_nf :
                    ¬(L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap
                        (Ptr.elemOffset s.locals.vals s.locals.curr.toNat)))
                      (L1.seq (L1.modify rbt_set_retval_curr) L1.throw) (rbt_set_found1 s)).failed :=
                  fun hf => h_mt.2 (h_seq2.2.mp hf)
                have h_chain := L1_seq_singleton_ok h_gm1.1 h_gm1.2
                  (m₂ := L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap
                      (Ptr.elemOffset s.locals.vals s.locals.curr.toNat)))
                    (L1.seq (L1.modify rbt_set_retval_curr) L1.throw))
                constructor
                · intro hf; exact h_inner2_nf (h_chain.2.mp hf)
                · intro r s' h_mem
                  rw [h_chain.1, h_inner2_res] at h_mem
                  have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                  subst hr; subst hs
                  exact rbt_found_branch_foundok s h_fv
              · -- key ≠ keys[curr]: skip (state unchanged, ok)
                intro s ⟨⟨h_inv, h_cond⟩, h_key_ne⟩
                constructor
                · intro h; exact h
                · intro r s' h_mem
                  have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                  match r with
                  | Except.ok () => subst hs; exact ⟨h_inv, h_cond⟩
                  | Except.error () => exact absurd hr (by intro h; cases h)
            · -- Second condition: left or right
              apply L1_hoare_condition
              · -- key < keys[curr]: go left
                intro s ⟨⟨h_inv, h_cond⟩, h_key_lt⟩
                have h_ne : s.locals.curr ≠ 4294967295 := by
                  simp at h_cond; exact h_cond
                obtain ⟨h_fv, h_f0, h_valid, h_dk, h_dv, h_dl, h_dr⟩ := h_inv
                have h_lv := h_valid.lefts_valid h_ne
                have h_gm := L1_guard_modify_result
                  (fun s : ProgramState => heapPtrValid s.globals.rawHeap
                      (Ptr.elemOffset s.locals.lefts s.locals.curr.toNat))
                  rbt_go_left s h_lv
                constructor
                · exact h_gm.2
                · intro r s' h_mem
                  rw [h_gm.1] at h_mem
                  have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                  subst hr; subst hs
                  exact rbt_go_left_preserves_inv s
                    ⟨h_fv, h_f0, h_valid, h_dk, h_dv, h_dl, h_dr⟩ h_ne
              · -- key >= keys[curr]: go right
                intro s ⟨⟨h_inv, h_cond⟩, h_key_ge⟩
                have h_ne : s.locals.curr ≠ 4294967295 := by
                  simp at h_cond; exact h_cond
                obtain ⟨h_fv, h_f0, h_valid, h_dk, h_dv, h_dl, h_dr⟩ := h_inv
                have h_rv := h_valid.rights_valid h_ne
                have h_gm := L1_guard_modify_result
                  (fun s : ProgramState => heapPtrValid s.globals.rawHeap
                      (Ptr.elemOffset s.locals.rights s.locals.curr.toNat))
                  rbt_go_right s h_rv
                constructor
                · exact h_gm.2
                · intro r s' h_mem
                  rw [h_gm.1] at h_mem
                  have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                  subst hr; subst hs
                  exact rbt_go_right_preserves_inv s
                    ⟨h_fv, h_f0, h_valid, h_dk, h_dv, h_dl, h_dr⟩ h_ne
          · -- exit: I ∧ curr = NULL → Q(ok) = I
            intro s h_inv _; exact h_inv
        · -- Teardown: modify retval0 >> throw
          intro s h_inv
          obtain ⟨h_fv, h_f0, h_valid, h_dk, h_dv, h_dl, h_dr⟩ := h_inv
          have h_mt := L1_modify_throw_result rbt_set_retval0 s
          constructor
          · exact h_mt.2
          · intro r s' h_mem
            rw [h_mt.1] at h_mem
            have ⟨hr, hs⟩ := Prod.mk.inj h_mem
            subst hr; subst hs
            exact rbt_teardown_foundok s h_f0
  · -- Handler: skip from FoundOk → post
    intro s h_foundok
    constructor
    · intro h; exact h
    · intro r s' h_mem
      have ⟨hr, hs⟩ := Prod.mk.inj h_mem
      subst hr; subst hs
      unfold rbt_lookup_spec; intro _; exact h_foundok
