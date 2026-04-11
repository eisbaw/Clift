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

theorem rbt_init_correct :
    rbt_init_spec.satisfiedBy Rbtree.l1_rbt_init_body := by
  sorry

theorem rbt_lookup_correct :
    rbt_lookup_spec.satisfiedBy Rbtree.l1_rbt_lookup_body := by
  sorry
