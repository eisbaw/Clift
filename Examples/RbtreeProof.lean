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

/-- rbt_lookup: BST search. Returns value if found, sets *found. -/
def rbt_lookup_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.t ∧
    heapPtrValid s.globals.rawHeap s.locals.found
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

theorem rbt_lookup_correct :
    rbt_lookup_spec.satisfiedBy Rbtree.l1_rbt_lookup_body := by
  sorry
