-- rb_count_above and rb_count_at_or_below validHoare proofs
-- TASK-0231: Postconditions use ListCountAboveIs/ListCountAtOrBelowIs.
-- These proofs have conditionals (if value > threshold) in the loop body.
-- Pattern: while-loop with conditional inside, following rb_count_nodes_validHoare.

import Examples.RBExtSpecs
open RingBufferExt

set_option maxHeartbeats 12800000
set_option maxRecDepth 4096

/-! ## Step functions for rb_count_above / rb_count_at_or_below

Both functions share the same step functions:
  - set count = 0
  - set cur = rb->head
  - count++
  - cur = cur->next
  - ret_val = count
-/

-- Step: count := 0
private noncomputable def rca_set_count0 (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, (0 : UInt32), s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

-- Step: cur := rb->head
private noncomputable def rca_set_cur_head (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, (hVal s.globals.rawHeap s.locals.rb).head,
    s.locals.current_count, s.locals.delta, s.locals.dst, s.locals.filled,
    s.locals.front, s.locals.idx, s.locals.iter, s.locals.max_drain,
    s.locals.max_val, s.locals.min_val, s.locals.modified, s.locals.n,
    s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

-- Step: count := count + 1
private noncomputable def rca_inc_count (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count + 1, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

-- Step: cur := cur->next
private noncomputable def rca_set_cur_next (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, (hVal s.globals.rawHeap s.locals.cur).next,
    s.locals.current_count, s.locals.delta, s.locals.dst, s.locals.filled,
    s.locals.front, s.locals.idx, s.locals.iter, s.locals.max_drain,
    s.locals.max_val, s.locals.min_val, s.locals.modified, s.locals.n,
    s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

-- Step: ret_val := count
private noncomputable def rca_set_ret_count (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.count,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

/-! ## Projection lemmas (two-layer approach for kernel depth) -/

-- rca_set_count0
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rca_set_count0_locals_eq (s : ProgramState) :
    (rca_set_count0 s).locals = ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
      s.locals.cb, (0 : UInt32), s.locals.cur, s.locals.current_count, s.locals.delta,
      s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
      s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
      s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
      s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
      s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
      s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
      s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
      s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
      s.locals.transferred, s.locals.val⟩ := by unfold rca_set_count0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
@[simp] private theorem rca_set_count0_globals (s : ProgramState) :
    (rca_set_count0 s).globals = s.globals := by unfold rca_set_count0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
@[simp] private theorem rca_set_count0_count (s : ProgramState) :
    (rca_set_count0 s).locals.count = 0 := by rw [rca_set_count0_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
@[simp] private theorem rca_set_count0_rb (s : ProgramState) :
    (rca_set_count0 s).locals.rb = s.locals.rb := by rw [rca_set_count0_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
@[simp] private theorem rca_set_count0_threshold (s : ProgramState) :
    (rca_set_count0 s).locals.threshold = s.locals.threshold := by rw [rca_set_count0_locals_eq]

-- rca_set_cur_head
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rca_set_cur_head_locals_eq (s : ProgramState) :
    (rca_set_cur_head s).locals = ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca,
      s.locals.cap, s.locals.cb, s.locals.count,
      (hVal s.globals.rawHeap s.locals.rb).head,
      s.locals.current_count, s.locals.delta, s.locals.dst, s.locals.filled,
      s.locals.front, s.locals.idx, s.locals.iter, s.locals.max_drain,
      s.locals.max_val, s.locals.min_val, s.locals.modified, s.locals.n,
      s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
      s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
      s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
      s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
      s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
      s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
      s.locals.transferred, s.locals.val⟩ := by unfold rca_set_cur_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
@[simp] private theorem rca_set_cur_head_globals (s : ProgramState) :
    (rca_set_cur_head s).globals = s.globals := by unfold rca_set_cur_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
@[simp] private theorem rca_set_cur_head_cur (s : ProgramState) :
    (rca_set_cur_head s).locals.cur =
      (hVal s.globals.rawHeap s.locals.rb).head := by rw [rca_set_cur_head_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
@[simp] private theorem rca_set_cur_head_rb (s : ProgramState) :
    (rca_set_cur_head s).locals.rb = s.locals.rb := by rw [rca_set_cur_head_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
@[simp] private theorem rca_set_cur_head_count (s : ProgramState) :
    (rca_set_cur_head s).locals.count = s.locals.count := by rw [rca_set_cur_head_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
@[simp] private theorem rca_set_cur_head_threshold (s : ProgramState) :
    (rca_set_cur_head s).locals.threshold = s.locals.threshold := by rw [rca_set_cur_head_locals_eq]

-- rca_inc_count
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rca_inc_count_locals_eq (s : ProgramState) :
    (rca_inc_count s).locals = ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
      s.locals.cb, s.locals.count + 1, s.locals.cur, s.locals.current_count,
      s.locals.delta, s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx,
      s.locals.iter, s.locals.max_drain, s.locals.max_val, s.locals.min_val,
      s.locals.modified, s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt,
      s.locals.old_head, s.locals.old_val, s.locals.out_val, s.locals.pop_ok,
      s.locals.pop_result, s.locals.prev, s.locals.push_ok, s.locals.push_result,
      s.locals.rb, s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
      s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
      s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
      s.locals.transferred, s.locals.val⟩ := by unfold rca_inc_count; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
@[simp] private theorem rca_inc_count_globals (s : ProgramState) :
    (rca_inc_count s).globals = s.globals := by unfold rca_inc_count; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
@[simp] private theorem rca_inc_count_count (s : ProgramState) :
    (rca_inc_count s).locals.count = s.locals.count + 1 := by rw [rca_inc_count_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
@[simp] private theorem rca_inc_count_cur (s : ProgramState) :
    (rca_inc_count s).locals.cur = s.locals.cur := by rw [rca_inc_count_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
@[simp] private theorem rca_inc_count_rb (s : ProgramState) :
    (rca_inc_count s).locals.rb = s.locals.rb := by rw [rca_inc_count_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
@[simp] private theorem rca_inc_count_threshold (s : ProgramState) :
    (rca_inc_count s).locals.threshold = s.locals.threshold := by rw [rca_inc_count_locals_eq]

-- rca_set_cur_next
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rca_set_cur_next_locals_eq (s : ProgramState) :
    (rca_set_cur_next s).locals = ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca,
      s.locals.cap, s.locals.cb, s.locals.count,
      (hVal s.globals.rawHeap s.locals.cur).next,
      s.locals.current_count, s.locals.delta, s.locals.dst, s.locals.filled,
      s.locals.front, s.locals.idx, s.locals.iter, s.locals.max_drain,
      s.locals.max_val, s.locals.min_val, s.locals.modified, s.locals.n,
      s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
      s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
      s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
      s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
      s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
      s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
      s.locals.transferred, s.locals.val⟩ := by unfold rca_set_cur_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
@[simp] private theorem rca_set_cur_next_globals (s : ProgramState) :
    (rca_set_cur_next s).globals = s.globals := by unfold rca_set_cur_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
@[simp] private theorem rca_set_cur_next_cur (s : ProgramState) :
    (rca_set_cur_next s).locals.cur =
      (hVal s.globals.rawHeap s.locals.cur).next := by rw [rca_set_cur_next_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
@[simp] private theorem rca_set_cur_next_count (s : ProgramState) :
    (rca_set_cur_next s).locals.count = s.locals.count := by rw [rca_set_cur_next_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
@[simp] private theorem rca_set_cur_next_rb (s : ProgramState) :
    (rca_set_cur_next s).locals.rb = s.locals.rb := by rw [rca_set_cur_next_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
@[simp] private theorem rca_set_cur_next_threshold (s : ProgramState) :
    (rca_set_cur_next s).locals.threshold = s.locals.threshold := by rw [rca_set_cur_next_locals_eq]

-- rca_set_ret_count
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rca_set_ret_count_locals_eq (s : ProgramState) :
    (rca_set_ret_count s).locals = ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
      s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
      s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
      s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
      s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
      s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
      s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
      s.locals.removed, s.locals.replaced, s.locals.result, s.locals.count,
      s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
      s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
      s.locals.transferred, s.locals.val⟩ := by unfold rca_set_ret_count; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
@[simp] private theorem rca_set_ret_count_globals (s : ProgramState) :
    (rca_set_ret_count s).globals = s.globals := by unfold rca_set_ret_count; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
@[simp] private theorem rca_set_ret_count_ret (s : ProgramState) :
    (rca_set_ret_count s).locals.ret__val = s.locals.count := by rw [rca_set_ret_count_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
@[simp] private theorem rca_set_ret_count_rb (s : ProgramState) :
    (rca_set_ret_count s).locals.rb = s.locals.rb := by rw [rca_set_ret_count_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
@[simp] private theorem rca_set_ret_count_threshold (s : ProgramState) :
    (rca_set_ret_count s).locals.threshold = s.locals.threshold := by rw [rca_set_ret_count_locals_eq]

/-! ## Funext lemmas -/

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rca_set_count0_funext :
    (fun s : ProgramState => { s with locals := { s.locals with count := (0 : UInt32) } }) = rca_set_count0 := by
  funext s; unfold rca_set_count0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rca_set_cur_head_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      cur := (hVal s.globals.rawHeap s.locals.rb).head } }) = rca_set_cur_head := by
  funext s; unfold rca_set_cur_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rca_inc_count_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      count := s.locals.count + 1 } }) = rca_inc_count := by
  funext s; unfold rca_inc_count; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rca_set_cur_next_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      cur := (hVal s.globals.rawHeap s.locals.cur).next } }) = rca_set_cur_next := by
  funext s; unfold rca_set_cur_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rca_set_ret_count_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      ret__val := s.locals.count } }) = rca_set_ret_count := by
  funext s; unfold rca_set_ret_count; rfl

/-! ## Loop invariant and postcondition for rb_count_above -/

-- Loop invariant: count + n_cur = n_head where n_cur = countAbove from cur
private def rca_inv (s : ProgramState) : Prop :=
  heapPtrValid s.globals.rawHeap s.locals.rb ∧
  ∃ (n_cur n_head : UInt32),
    ListCountAboveIs s.globals.rawHeap s.locals.cur s.locals.threshold n_cur ∧
    ListCountAboveIs s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head
        s.locals.threshold n_head ∧
    s.locals.count + n_cur = n_head

-- Intermediate after condition, before cur advance: count + tail_count = n_head
-- Here "tail_count" is the count from cur->next (not cur itself).
-- cur is still the old value, but count has been adjusted.
private def rca_mid (s : ProgramState) : Prop :=
  heapPtrValid s.globals.rawHeap s.locals.rb ∧
  s.locals.cur ≠ Ptr.null ∧
  heapPtrValid s.globals.rawHeap s.locals.cur ∧
  ∃ (n_tail n_head : UInt32),
    ListCountAboveIs s.globals.rawHeap (hVal s.globals.rawHeap s.locals.cur).next
        s.locals.threshold n_tail ∧
    ListCountAboveIs s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head
        s.locals.threshold n_head ∧
    s.locals.count + n_tail = n_head

-- Postcondition delivered on throw (for catch handler)
private def rca_post (s : ProgramState) : Prop :=
  ∃ n, ListCountAboveIs s.globals.rawHeap
         (hVal s.globals.rawHeap s.locals.rb).head s.locals.threshold n ∧
       s.locals.ret__val = n

-- After-while intermediate
private def rca_after_while (s : ProgramState) : Prop :=
  heapPtrValid s.globals.rawHeap s.locals.rb ∧
  ∃ n_head : UInt32,
    ListCountAboveIs s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head
        s.locals.threshold n_head ∧
    s.locals.count = n_head

/-! ## Main proof: rb_count_above_validHoare -/

set_option maxRecDepth 8192 in
set_option maxHeartbeats 25600000 in
attribute [local irreducible] hVal heapUpdate heapPtrValid
  rca_set_count0 rca_set_cur_head rca_inc_count rca_set_cur_next rca_set_ret_count in
theorem rb_count_above_validHoare :
    rb_count_above_spec.satisfiedBy RingBufferExt.l1_rb_count_above_body := by
  unfold FuncSpec.satisfiedBy rb_count_above_spec
  unfold RingBufferExt.l1_rb_count_above_body
  simp only [rca_set_count0_funext, rca_set_cur_head_funext, rca_inc_count_funext,
    rca_set_cur_next_funext, rca_set_ret_count_funext]
  apply L1_hoare_catch (R := rca_post)
  · -- Body (inside catch): must produce rca_post on error/throw
    apply L1_hoare_seq (R := fun s =>
      heapPtrValid s.globals.rawHeap s.locals.rb ∧
      LinkedListValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head ∧
      s.locals.count = 0)
    · -- modify count=0: preserves pre + sets count=0
      intro s₀ ⟨hrb, hll⟩
      constructor
      · intro h; exact h
      · intro r s₁ h_mem
        have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
        exact ⟨by simp only [rca_set_count0_globals, rca_set_count0_rb]; exact hrb,
               by simp only [rca_set_count0_globals, rca_set_count0_rb]; exact hll,
               rca_set_count0_count s₀⟩
    · -- rest: seq (guard+modify) (seq while teardown)
      apply L1_hoare_seq (R := rca_inv)
      · -- guard+modify: establish invariant (cur=head, count=0)
        intro s₀ ⟨hrb, hll, hc0⟩
        have h_gm := L1_guard_modify_result
          (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
          rca_set_cur_head s₀ hrb
        constructor
        · exact h_gm.2
        · intro r s₁ h_mem
          rw [h_gm.1] at h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
          unfold rca_inv
          constructor
          · simp only [rca_set_cur_head_globals, rca_set_cur_head_rb]; exact hrb
          · obtain ⟨n_head, hn_head⟩ := hll.hasCountAbove s₀.locals.threshold
            refine ⟨n_head, n_head, ?_, ?_, ?_⟩
            · simp only [rca_set_cur_head_globals, rca_set_cur_head_cur,
                rca_set_cur_head_threshold]
              exact hn_head
            · simp only [rca_set_cur_head_globals, rca_set_cur_head_rb,
                rca_set_cur_head_threshold]
              exact hn_head
            · rw [rca_set_cur_head_count, hc0]; simp
      · -- seq while teardown
        apply L1_hoare_seq (R := rca_after_while)
        · -- while loop: rca_inv → rca_after_while
          apply L1_hoare_while_from_body (I := rca_inv)
          · -- loop body: seq (condition ...) (seq (guard curValid) (modify cur=next))
            -- Use rca_mid as intermediate between condition and guard+modify
            apply L1_hoare_seq
              (P := fun s => rca_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
              (R := rca_mid)
            · -- condition: if value > threshold then count++ else skip
              apply L1_hoare_condition
              · -- true branch: value > threshold → count++
                intro s hpre
                obtain ⟨⟨h_inv, h_cond⟩, h_match⟩ := hpre
                -- Pre-decompose before entering validHoare obligations
                unfold rca_inv at h_inv
                obtain ⟨h_rb, n_cur, n_head, h_cnt_cur, h_cnt_head, h_sum⟩ := h_inv
                have h_ne : s.locals.cur ≠ Ptr.null := by
                  simp only [decide_eq_true_eq] at h_cond; exact h_cond
                have ⟨h_valid_cur, h_cases⟩ := h_cnt_cur.decompose h_ne
                have h_mid : rca_mid (rca_inc_count s) := by
                  unfold rca_mid
                  rcases h_cases with ⟨h_above, m, h_eq, h_cnt_tail⟩ | ⟨h_not, h_cnt_tail⟩
                  · -- above case: n_cur = m + 1
                    exact ⟨by simp only [rca_inc_count_globals, rca_inc_count_rb]; exact h_rb,
                           by simp only [rca_inc_count_cur]; exact h_ne,
                           by simp only [rca_inc_count_globals, rca_inc_count_cur]; exact h_valid_cur,
                           m, n_head,
                           by simp only [rca_inc_count_globals, rca_inc_count_cur,
                              rca_inc_count_threshold]; exact h_cnt_tail,
                           by simp only [rca_inc_count_globals, rca_inc_count_rb,
                              rca_inc_count_threshold]; exact h_cnt_head,
                           by simp only [rca_inc_count_count]; subst h_eq;
                              rw [show s.locals.count + 1 + m = s.locals.count + (m + 1) from by ac_rfl];
                              exact h_sum⟩
                  · -- not-above: contradicts condition true
                    exfalso
                    simp only [decide_eq_true_eq] at h_match
                    exact h_not h_match
                constructor
                · intro hf; exact hf
                · intro r s' h_mem
                  have ⟨_, hs⟩ := Prod.mk.inj h_mem
                  match r with
                  | Except.ok () => rw [hs]; exact h_mid
                  | Except.error () =>
                    exact absurd (Prod.mk.inj h_mem).1 (by intro h; cases h)
              · -- false branch: not (value > threshold) → skip (no state change)
                intro s hpre
                obtain ⟨⟨h_inv, h_cond⟩, h_nomatch⟩ := hpre
                -- Pre-decompose rca_inv before entering the validHoare
                unfold rca_inv at h_inv
                obtain ⟨h_rb, n_cur, n_head, h_cnt_cur, h_cnt_head, h_sum⟩ := h_inv
                have h_ne : s.locals.cur ≠ Ptr.null := by
                  simp only [decide_eq_true_eq] at h_cond; exact h_cond
                have ⟨h_valid_cur, h_cases⟩ := h_cnt_cur.decompose h_ne
                -- Resolve which case we're in
                have h_mid : rca_mid s := by
                  unfold rca_mid
                  rcases h_cases with ⟨h_above, m, h_eq, h_cnt_tail⟩ | ⟨h_not, h_cnt_tail⟩
                  · -- above: contradicts condition false
                    exfalso
                    simp only [decide_eq_false_iff_not] at h_nomatch
                    exact h_nomatch h_above
                  · -- not above: count unchanged
                    exact ⟨h_rb, h_ne, h_valid_cur, n_cur, n_head, h_cnt_tail, h_cnt_head, h_sum⟩
                constructor
                · intro hf; exact hf
                · intro r s' h_mem
                  have ⟨_, hs⟩ := Prod.mk.inj h_mem
                  match r with
                  | Except.ok () => rw [hs]; exact h_mid
                  | Except.error () =>
                    exact absurd (Prod.mk.inj h_mem).1 (by intro h; cases h)
            · -- guard cur valid, then cur := cur->next
              -- Precondition is rca_mid: we already have heapPtrValid cur and tail count
              intro s hpre
              unfold rca_mid at hpre
              obtain ⟨h_rb, h_ne, h_valid_cur, n_tail, n_head, h_cnt_tail, h_cnt_head, h_sum⟩ := hpre
              have h_gm := L1_guard_modify_result
                (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cur)
                rca_set_cur_next s h_valid_cur
              constructor
              · exact h_gm.2
              · intro r s' h_mem
                rw [h_gm.1] at h_mem
                have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
                -- Re-establish rca_inv with cur = old_cur->next
                show rca_inv (rca_set_cur_next s)
                unfold rca_inv
                constructor
                · simp only [rca_set_cur_next_globals, rca_set_cur_next_rb]; exact h_rb
                · refine ⟨n_tail, n_head, ?_, ?_, ?_⟩
                  · simp only [rca_set_cur_next_globals, rca_set_cur_next_cur,
                      rca_set_cur_next_threshold]
                    exact h_cnt_tail
                  · simp only [rca_set_cur_next_globals, rca_set_cur_next_rb,
                      rca_set_cur_next_threshold]
                    exact h_cnt_head
                  · simp only [rca_set_cur_next_count]; exact h_sum
          · -- exit: cur = null, I holds → rca_after_while
            intro s h_inv h_false
            show rca_after_while s
            unfold rca_inv at h_inv
            obtain ⟨h_rb, n_cur, n_head, h_cnt_cur, h_cnt_head, h_sum⟩ := h_inv
            have h_null : s.locals.cur = Ptr.null := by
              simp only [decide_eq_false_iff_not, ne_eq, Decidable.not_not] at h_false
              exact h_false
            rw [h_null] at h_cnt_cur
            have h_zero := h_cnt_cur.null_zero
            subst h_zero
            unfold rca_after_while
            refine ⟨h_rb, n_head, h_cnt_head, ?_⟩
            simp at h_sum; exact h_sum
        · -- teardown: seq (modify ret=count) throw → must produce rca_post on error
          intro s h_aw
          unfold rca_after_while at h_aw
          obtain ⟨h_rb, n_head, h_cnt_head, h_count_eq⟩ := h_aw
          have h_mt := L1_modify_throw_result rca_set_ret_count s
          constructor
          · exact h_mt.2
          · intro r s' h_mem
            rw [h_mt.1] at h_mem
            have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
            show rca_post (rca_set_ret_count s)
            unfold rca_post
            exact ⟨n_head,
              by rw [rca_set_ret_count_globals, rca_set_ret_count_rb,
                     rca_set_ret_count_threshold]; exact h_cnt_head,
              by rw [rca_set_ret_count_ret]; exact h_count_eq⟩
  · -- handler: skip — rca_post → spec postcondition
    intro s h_post
    constructor
    · intro hf; exact hf
    · intro r s' h_mem
      have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
      intro _
      unfold rca_post at h_post
      exact h_post

/-! ## Loop invariant and postcondition for rb_count_at_or_below -/

-- Loop invariant
private def rcb_inv (s : ProgramState) : Prop :=
  heapPtrValid s.globals.rawHeap s.locals.rb ∧
  ∃ (n_cur n_head : UInt32),
    ListCountAtOrBelowIs s.globals.rawHeap s.locals.cur s.locals.threshold n_cur ∧
    ListCountAtOrBelowIs s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head
        s.locals.threshold n_head ∧
    s.locals.count + n_cur = n_head

-- Intermediate after condition, before cur advance
private def rcb_mid (s : ProgramState) : Prop :=
  heapPtrValid s.globals.rawHeap s.locals.rb ∧
  s.locals.cur ≠ Ptr.null ∧
  heapPtrValid s.globals.rawHeap s.locals.cur ∧
  ∃ (n_tail n_head : UInt32),
    ListCountAtOrBelowIs s.globals.rawHeap (hVal s.globals.rawHeap s.locals.cur).next
        s.locals.threshold n_tail ∧
    ListCountAtOrBelowIs s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head
        s.locals.threshold n_head ∧
    s.locals.count + n_tail = n_head

-- Postcondition delivered on throw
private def rcb_post (s : ProgramState) : Prop :=
  ∃ n, ListCountAtOrBelowIs s.globals.rawHeap
         (hVal s.globals.rawHeap s.locals.rb).head s.locals.threshold n ∧
       s.locals.ret__val = n

-- After-while intermediate
private def rcb_after_while (s : ProgramState) : Prop :=
  heapPtrValid s.globals.rawHeap s.locals.rb ∧
  ∃ n_head : UInt32,
    ListCountAtOrBelowIs s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head
        s.locals.threshold n_head ∧
    s.locals.count = n_head

/-! ## Main proof: rb_count_at_or_below_validHoare -/

set_option maxRecDepth 8192 in
set_option maxHeartbeats 25600000 in
attribute [local irreducible] hVal heapUpdate heapPtrValid
  rca_set_count0 rca_set_cur_head rca_inc_count rca_set_cur_next rca_set_ret_count in
theorem rb_count_at_or_below_validHoare :
    rb_count_at_or_below_spec.satisfiedBy RingBufferExt.l1_rb_count_at_or_below_body := by
  unfold FuncSpec.satisfiedBy rb_count_at_or_below_spec
  unfold RingBufferExt.l1_rb_count_at_or_below_body
  simp only [rca_set_count0_funext, rca_set_cur_head_funext, rca_inc_count_funext,
    rca_set_cur_next_funext, rca_set_ret_count_funext]
  apply L1_hoare_catch (R := rcb_post)
  · -- Body (inside catch)
    apply L1_hoare_seq (R := fun s =>
      heapPtrValid s.globals.rawHeap s.locals.rb ∧
      LinkedListValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head ∧
      s.locals.count = 0)
    · -- modify count=0
      intro s₀ ⟨hrb, hll⟩
      constructor
      · intro h; exact h
      · intro r s₁ h_mem
        have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
        exact ⟨by simp only [rca_set_count0_globals, rca_set_count0_rb]; exact hrb,
               by simp only [rca_set_count0_globals, rca_set_count0_rb]; exact hll,
               rca_set_count0_count s₀⟩
    · apply L1_hoare_seq (R := rcb_inv)
      · -- guard+modify: establish invariant
        intro s₀ ⟨hrb, hll, hc0⟩
        have h_gm := L1_guard_modify_result
          (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
          rca_set_cur_head s₀ hrb
        constructor
        · exact h_gm.2
        · intro r s₁ h_mem
          rw [h_gm.1] at h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
          unfold rcb_inv
          constructor
          · simp only [rca_set_cur_head_globals, rca_set_cur_head_rb]; exact hrb
          · obtain ⟨n_head, hn_head⟩ := hll.hasCountAtOrBelow s₀.locals.threshold
            refine ⟨n_head, n_head, ?_, ?_, ?_⟩
            · simp only [rca_set_cur_head_globals, rca_set_cur_head_cur,
                rca_set_cur_head_threshold]
              exact hn_head
            · simp only [rca_set_cur_head_globals, rca_set_cur_head_rb,
                rca_set_cur_head_threshold]
              exact hn_head
            · rw [rca_set_cur_head_count, hc0]; simp
      · apply L1_hoare_seq (R := rcb_after_while)
        · -- while loop
          apply L1_hoare_while_from_body (I := rcb_inv)
          · apply L1_hoare_seq
              (P := fun s => rcb_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
              (R := rcb_mid)
            · -- condition: if value <= threshold then count++ else skip
              apply L1_hoare_condition
              · -- true branch: value <= threshold → count++
                intro s hpre
                obtain ⟨⟨h_inv, h_cond⟩, h_match⟩ := hpre
                unfold rcb_inv at h_inv
                obtain ⟨h_rb, n_cur, n_head, h_cnt_cur, h_cnt_head, h_sum⟩ := h_inv
                have h_ne : s.locals.cur ≠ Ptr.null := by
                  simp only [decide_eq_true_eq] at h_cond; exact h_cond
                have ⟨h_valid_cur, h_cases⟩ := h_cnt_cur.decompose h_ne
                have h_mid : rcb_mid (rca_inc_count s) := by
                  unfold rcb_mid
                  rcases h_cases with ⟨h_leq, m, h_eq, h_cnt_tail⟩ | ⟨h_not, h_cnt_tail⟩
                  · exact ⟨by simp only [rca_inc_count_globals, rca_inc_count_rb]; exact h_rb,
                           by simp only [rca_inc_count_cur]; exact h_ne,
                           by simp only [rca_inc_count_globals, rca_inc_count_cur]; exact h_valid_cur,
                           m, n_head,
                           by simp only [rca_inc_count_globals, rca_inc_count_cur,
                              rca_inc_count_threshold]; exact h_cnt_tail,
                           by simp only [rca_inc_count_globals, rca_inc_count_rb,
                              rca_inc_count_threshold]; exact h_cnt_head,
                           by simp only [rca_inc_count_count]; subst h_eq;
                              rw [show s.locals.count + 1 + m = s.locals.count + (m + 1) from by ac_rfl];
                              exact h_sum⟩
                  · exfalso
                    simp only [decide_eq_true_eq] at h_match
                    exact h_not h_match
                constructor
                · intro hf; exact hf
                · intro r s' h_mem
                  have ⟨_, hs⟩ := Prod.mk.inj h_mem
                  match r with
                  | Except.ok () => rw [hs]; exact h_mid
                  | Except.error () =>
                    exact absurd (Prod.mk.inj h_mem).1 (by intro h; cases h)
              · -- false branch: ¬(value <= threshold) → skip
                intro s hpre
                obtain ⟨⟨h_inv, h_cond⟩, h_nomatch⟩ := hpre
                unfold rcb_inv at h_inv
                obtain ⟨h_rb, n_cur, n_head, h_cnt_cur, h_cnt_head, h_sum⟩ := h_inv
                have h_ne : s.locals.cur ≠ Ptr.null := by
                  simp only [decide_eq_true_eq] at h_cond; exact h_cond
                have ⟨h_valid_cur, h_cases⟩ := h_cnt_cur.decompose h_ne
                have h_mid : rcb_mid s := by
                  unfold rcb_mid
                  rcases h_cases with ⟨h_leq, m, h_eq, h_cnt_tail⟩ | ⟨h_not, h_cnt_tail⟩
                  · exfalso
                    simp only [decide_eq_false_iff_not] at h_nomatch
                    exact h_nomatch h_leq
                  · exact ⟨h_rb, h_ne, h_valid_cur, n_cur, n_head, h_cnt_tail, h_cnt_head, h_sum⟩
                constructor
                · intro hf; exact hf
                · intro r s' h_mem
                  have ⟨_, hs⟩ := Prod.mk.inj h_mem
                  match r with
                  | Except.ok () => rw [hs]; exact h_mid
                  | Except.error () =>
                    exact absurd (Prod.mk.inj h_mem).1 (by intro h; cases h)
            · -- guard cur valid, then cur := cur->next
              intro s hpre
              unfold rcb_mid at hpre
              obtain ⟨h_rb, h_ne, h_valid_cur, n_tail, n_head, h_cnt_tail, h_cnt_head, h_sum⟩ := hpre
              have h_gm := L1_guard_modify_result
                (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cur)
                rca_set_cur_next s h_valid_cur
              constructor
              · exact h_gm.2
              · intro r s' h_mem
                rw [h_gm.1] at h_mem
                have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
                show rcb_inv (rca_set_cur_next s)
                unfold rcb_inv
                constructor
                · simp only [rca_set_cur_next_globals, rca_set_cur_next_rb]; exact h_rb
                · refine ⟨n_tail, n_head, ?_, ?_, ?_⟩
                  · simp only [rca_set_cur_next_globals, rca_set_cur_next_cur,
                      rca_set_cur_next_threshold]
                    exact h_cnt_tail
                  · simp only [rca_set_cur_next_globals, rca_set_cur_next_rb,
                      rca_set_cur_next_threshold]
                    exact h_cnt_head
                  · simp only [rca_set_cur_next_count]; exact h_sum
          · -- exit: cur = null → rcb_after_while
            intro s h_inv h_false
            show rcb_after_while s
            unfold rcb_inv at h_inv
            obtain ⟨h_rb, n_cur, n_head, h_cnt_cur, h_cnt_head, h_sum⟩ := h_inv
            have h_null : s.locals.cur = Ptr.null := by
              simp only [decide_eq_false_iff_not, ne_eq, Decidable.not_not] at h_false
              exact h_false
            rw [h_null] at h_cnt_cur
            have h_zero := h_cnt_cur.null_zero
            subst h_zero
            unfold rcb_after_while
            refine ⟨h_rb, n_head, h_cnt_head, ?_⟩
            simp at h_sum; exact h_sum
        · -- teardown
          intro s h_aw
          unfold rcb_after_while at h_aw
          obtain ⟨h_rb, n_head, h_cnt_head, h_count_eq⟩ := h_aw
          have h_mt := L1_modify_throw_result rca_set_ret_count s
          constructor
          · exact h_mt.2
          · intro r s' h_mem
            rw [h_mt.1] at h_mem
            have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
            show rcb_post (rca_set_ret_count s)
            unfold rcb_post
            exact ⟨n_head,
              by rw [rca_set_ret_count_globals, rca_set_ret_count_rb,
                     rca_set_ret_count_threshold]; exact h_cnt_head,
              by rw [rca_set_ret_count_ret]; exact h_count_eq⟩
  · -- handler: skip
    intro s h_post
    constructor
    · intro hf; exact hf
    · intro r s' h_mem
      have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
      intro _
      unfold rcb_post at h_post
      exact h_post
