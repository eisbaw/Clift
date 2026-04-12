-- Proof for rb_equal_validHoare (split from RBExtProofsSorry for memory)
import Examples.RBExtSpecs
set_option maxHeartbeats 25600000
set_option maxRecDepth 4096
open RingBufferExt

-- Invariant: both cursors point to valid linked lists
private def rb_equal_inv (s : ProgramState) : Prop :=
  LinkedListValid s.globals.rawHeap s.locals.ca ∧
  LinkedListValid s.globals.rawHeap s.locals.cb

-- Return predicate: ret__val is 0 or 1
private def rb_equal_ret_bool (s : ProgramState) : Prop :=
  s.locals.ret__val = 0 ∨ s.locals.ret__val = 1

-- Step functions (anonymous constructors to avoid kernel depth issues)
private noncomputable def rb_equal_set_ret0 (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, (0 : UInt32),
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

private noncomputable def rb_equal_set_ret1 (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, (1 : UInt32),
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

private noncomputable def rb_equal_set_ca (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b,
    (hVal s.globals.rawHeap s.locals.a).head, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

private noncomputable def rb_equal_set_cb (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    (hVal s.globals.rawHeap s.locals.b).head,
    s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

private noncomputable def rb_equal_set_ca_next (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b,
    (hVal s.globals.rawHeap s.locals.ca).next, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

private noncomputable def rb_equal_set_cb_next (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    (hVal s.globals.rawHeap s.locals.cb).next,
    s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

-- Projection lemmas: globals preservation
private theorem rb_equal_set_ca_globals (s : ProgramState) :
    (rb_equal_set_ca s).globals = s.globals := by
  unfold rb_equal_set_ca; rfl

private theorem rb_equal_set_cb_globals (s : ProgramState) :
    (rb_equal_set_cb s).globals = s.globals := by
  unfold rb_equal_set_cb; rfl

private theorem rb_equal_set_ca_next_globals (s : ProgramState) :
    (rb_equal_set_ca_next s).globals = s.globals := by
  unfold rb_equal_set_ca_next; rfl

private theorem rb_equal_set_cb_next_globals (s : ProgramState) :
    (rb_equal_set_cb_next s).globals = s.globals := by
  unfold rb_equal_set_cb_next; rfl

-- Projection lemmas: locals_eq
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_equal_set_ret0_locals_eq (s : ProgramState) :
    (rb_equal_set_ret0 s).locals = ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca,
      s.locals.cap, s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count,
      s.locals.delta, s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx,
      s.locals.iter, s.locals.max_drain, s.locals.max_val, s.locals.min_val,
      s.locals.modified, s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt,
      s.locals.old_head, s.locals.old_val, s.locals.out_val, s.locals.pop_ok,
      s.locals.pop_result, s.locals.prev, s.locals.push_ok, s.locals.push_result,
      s.locals.rb, s.locals.removed, s.locals.replaced, s.locals.result, (0 : UInt32),
      s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
      s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
      s.locals.transferred, s.locals.val⟩ := by
  unfold rb_equal_set_ret0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_equal_set_ret0_locals_ret (s : ProgramState) :
    (rb_equal_set_ret0 s).locals.ret__val = 0 := by
  rw [rb_equal_set_ret0_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_equal_set_ret1_locals_eq (s : ProgramState) :
    (rb_equal_set_ret1 s).locals = ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca,
      s.locals.cap, s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count,
      s.locals.delta, s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx,
      s.locals.iter, s.locals.max_drain, s.locals.max_val, s.locals.min_val,
      s.locals.modified, s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt,
      s.locals.old_head, s.locals.old_val, s.locals.out_val, s.locals.pop_ok,
      s.locals.pop_result, s.locals.prev, s.locals.push_ok, s.locals.push_result,
      s.locals.rb, s.locals.removed, s.locals.replaced, s.locals.result, (1 : UInt32),
      s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
      s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
      s.locals.transferred, s.locals.val⟩ := by
  unfold rb_equal_set_ret1; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_equal_set_ret1_locals_ret (s : ProgramState) :
    (rb_equal_set_ret1 s).locals.ret__val = 1 := by
  rw [rb_equal_set_ret1_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_equal_set_ca_locals_eq (s : ProgramState) :
    (rb_equal_set_ca s).locals = ⟨s.locals.a, s.locals.actual, s.locals.b,
      (hVal s.globals.rawHeap s.locals.a).head, s.locals.cap,
      s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
      s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
      s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
      s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
      s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
      s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
      s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
      s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
      s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
      s.locals.transferred, s.locals.val⟩ := by
  unfold rb_equal_set_ca; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_equal_set_ca_locals_ca (s : ProgramState) :
    (rb_equal_set_ca s).locals.ca = (hVal s.globals.rawHeap s.locals.a).head := by
  rw [rb_equal_set_ca_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_equal_set_ca_locals_cb (s : ProgramState) :
    (rb_equal_set_ca s).locals.cb = s.locals.cb := by
  rw [rb_equal_set_ca_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_equal_set_cb_locals_eq (s : ProgramState) :
    (rb_equal_set_cb s).locals = ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca,
      s.locals.cap, (hVal s.globals.rawHeap s.locals.b).head,
      s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
      s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
      s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
      s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
      s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
      s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
      s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
      s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
      s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
      s.locals.transferred, s.locals.val⟩ := by
  unfold rb_equal_set_cb; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_equal_set_cb_locals_cb (s : ProgramState) :
    (rb_equal_set_cb s).locals.cb = (hVal s.globals.rawHeap s.locals.b).head := by
  rw [rb_equal_set_cb_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_equal_set_cb_locals_ca (s : ProgramState) :
    (rb_equal_set_cb s).locals.ca = s.locals.ca := by
  rw [rb_equal_set_cb_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_equal_set_ca_next_locals_eq (s : ProgramState) :
    (rb_equal_set_ca_next s).locals = ⟨s.locals.a, s.locals.actual, s.locals.b,
      (hVal s.globals.rawHeap s.locals.ca).next, s.locals.cap,
      s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
      s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
      s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
      s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
      s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
      s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
      s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
      s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
      s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
      s.locals.transferred, s.locals.val⟩ := by
  unfold rb_equal_set_ca_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_equal_set_ca_next_locals_ca (s : ProgramState) :
    (rb_equal_set_ca_next s).locals.ca = (hVal s.globals.rawHeap s.locals.ca).next := by
  rw [rb_equal_set_ca_next_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_equal_set_ca_next_locals_cb (s : ProgramState) :
    (rb_equal_set_ca_next s).locals.cb = s.locals.cb := by
  rw [rb_equal_set_ca_next_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_equal_set_cb_next_locals_eq (s : ProgramState) :
    (rb_equal_set_cb_next s).locals = ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca,
      s.locals.cap, (hVal s.globals.rawHeap s.locals.cb).next,
      s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
      s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
      s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
      s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
      s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
      s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
      s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
      s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
      s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
      s.locals.transferred, s.locals.val⟩ := by
  unfold rb_equal_set_cb_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_equal_set_cb_next_locals_cb (s : ProgramState) :
    (rb_equal_set_cb_next s).locals.cb = (hVal s.globals.rawHeap s.locals.cb).next := by
  rw [rb_equal_set_cb_next_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_equal_set_cb_next_locals_ca (s : ProgramState) :
    (rb_equal_set_cb_next s).locals.ca = s.locals.ca := by
  rw [rb_equal_set_cb_next_locals_eq]

-- funext lemmas
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_equal_set_ret0_funext :
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := (0 : UInt32) } }) =
      rb_equal_set_ret0 := by
  funext s; unfold rb_equal_set_ret0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_equal_set_ret1_funext :
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := (1 : UInt32) } }) =
      rb_equal_set_ret1 := by
  funext s; unfold rb_equal_set_ret1; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_equal_set_ca_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      ca := (hVal s.globals.rawHeap s.locals.a).head } }) = rb_equal_set_ca := by
  funext s; unfold rb_equal_set_ca; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_equal_set_cb_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      cb := (hVal s.globals.rawHeap s.locals.b).head } }) = rb_equal_set_cb := by
  funext s; unfold rb_equal_set_cb; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_equal_set_ca_next_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      ca := (hVal s.globals.rawHeap s.locals.ca).next } }) = rb_equal_set_ca_next := by
  funext s; unfold rb_equal_set_ca_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_equal_set_cb_next_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      cb := (hVal s.globals.rawHeap s.locals.cb).next } }) = rb_equal_set_cb_next := by
  funext s; unfold rb_equal_set_cb_next; rfl

-- Main theorem
attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem rb_equal_validHoare :
    rb_equal_spec.satisfiedBy RingBufferExt.l1_rb_equal_body := by
  unfold FuncSpec.satisfiedBy rb_equal_spec
  unfold RingBufferExt.l1_rb_equal_body
  simp only [rb_equal_set_ret0_funext, rb_equal_set_ret1_funext,
    rb_equal_set_ca_funext, rb_equal_set_cb_funext,
    rb_equal_set_ca_next_funext, rb_equal_set_cb_next_funext]
  apply L1_hoare_catch (R := rb_equal_ret_bool)
  · -- body inside catch
    -- Structure: seq(cond(count_ne, ret0+throw, skip), rest)
    apply L1_hoare_seq
      (R := fun s => heapPtrValid s.globals.rawHeap s.locals.a ∧
                      heapPtrValid s.globals.rawHeap s.locals.b ∧
                      LinkedListValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.a).head ∧
                      LinkedListValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.b).head)
    · -- cond: count mismatch → ret=0, throw; else skip
      apply L1_hoare_condition
      · -- true branch: counts differ → modify ret=0, throw
        intro s hpre
        obtain ⟨⟨h_a, h_b, h_lla, h_llb⟩, _⟩ := hpre
        have h_mt := L1_modify_throw_result rb_equal_set_ret0 s
        constructor
        · exact h_mt.2
        · intro r s' h_mem
          rw [h_mt.1] at h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem
          subst hr; subst hs
          unfold rb_equal_ret_bool
          left; rw [rb_equal_set_ret0_locals_ret]
      · -- false branch: counts equal → skip
        intro s hpre
        obtain ⟨⟨h_a, h_b, h_lla, h_llb⟩, _⟩ := hpre
        constructor
        · intro hf; exact hf
        · intro r s' h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem
          match r with
          | Except.ok () => subst hs; exact ⟨h_a, h_b, h_lla, h_llb⟩
          | Except.error () => exact absurd hr (by intro h; cases h)
    · -- rest: guard+ca := a.head >> guard+cb := b.head >> while >> postloop
      apply L1_hoare_seq (R := fun s =>
        heapPtrValid s.globals.rawHeap s.locals.b ∧
        LinkedListValid s.globals.rawHeap s.locals.ca ∧
        LinkedListValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.b).head)
      · -- guard(heapPtrValid a) >> ca := a.head
        intro s hpre
        obtain ⟨h_a, h_b, h_lla, h_llb⟩ := hpre
        have h_gm := L1_guard_modify_result
          (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.a)
          rb_equal_set_ca s h_a
        constructor
        · exact h_gm.2
        · intro r s' h_mem
          rw [h_gm.1] at h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem
          subst hr; subst hs
          refine ⟨?_, ?_, ?_⟩
          · rw [rb_equal_set_ca_globals]; exact h_b
          · rw [rb_equal_set_ca_locals_ca, rb_equal_set_ca_globals]; exact h_lla
          · rw [rb_equal_set_ca_globals]; exact h_llb
      · -- guard+cb := b.head >> while >> postloop
        apply L1_hoare_seq (R := rb_equal_inv)
        · -- guard(heapPtrValid b) >> cb := b.head
          intro s hpre
          obtain ⟨h_b, h_ca_ll, h_llb⟩ := hpre
          have h_gm := L1_guard_modify_result
            (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.b)
            rb_equal_set_cb s h_b
          constructor
          · exact h_gm.2
          · intro r s' h_mem
            rw [h_gm.1] at h_mem
            have ⟨hr, hs⟩ := Prod.mk.inj h_mem
            subst hr; subst hs
            unfold rb_equal_inv
            exact ⟨by rw [rb_equal_set_cb_globals, rb_equal_set_cb_locals_ca]; exact h_ca_ll,
                   by rw [rb_equal_set_cb_locals_cb, rb_equal_set_cb_globals]; exact h_llb⟩
        · -- while >> postloop
          apply L1_hoare_seq (R := rb_equal_inv)
          · -- while loop
            apply L1_hoare_while_from_body
            · -- loop body
              -- Structure: seq(cond(cb=null,...), seq(cond(value_ne,...), seq(guard+ca_next, guard+cb_next)))
              -- Use R that tracks both cursors non-null after the two conds
              apply L1_hoare_seq
                (P := fun s => rb_equal_inv s ∧ decide (s.locals.ca ≠ Ptr.null) = true)
                (R := fun s => rb_equal_inv s ∧ s.locals.ca ≠ Ptr.null ∧ s.locals.cb ≠ Ptr.null)
              · -- cond(cb = null, ret0+throw, skip)
                apply L1_hoare_condition
                · -- true: cb is null → ret=0, throw (early exit)
                  intro s hpre
                  obtain ⟨⟨h_inv, h_cond⟩, _⟩ := hpre
                  have h_mt := L1_modify_throw_result rb_equal_set_ret0 s
                  constructor
                  · exact h_mt.2
                  · intro r s' h_mem
                    rw [h_mt.1] at h_mem
                    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                    subst hr; subst hs
                    unfold rb_equal_ret_bool
                    left; rw [rb_equal_set_ret0_locals_ret]
                · -- false: cb ≠ null → skip, track cb ≠ null
                  intro s hpre
                  obtain ⟨⟨h_inv, h_ca_cond⟩, h_cb_cond⟩ := hpre
                  constructor
                  · intro hf; exact hf
                  · intro r s' h_mem
                    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                    match r with
                    | Except.ok () =>
                      subst hs
                      refine ⟨h_inv, ?_, ?_⟩
                      · simp only [decide_eq_true_eq] at h_ca_cond; exact h_ca_cond
                      · -- decide (cb = null) = false means cb ≠ null
                        simp only [decide_eq_true_eq] at h_cb_cond
                        exact fun h => h_cb_cond h
                    | Except.error () => exact absurd hr (by intro h; cases h)
              · -- seq(cond(value_ne,...), seq(guard+ca_next, guard+cb_next))
                apply L1_hoare_seq
                  (P := fun s => rb_equal_inv s ∧ s.locals.ca ≠ Ptr.null ∧ s.locals.cb ≠ Ptr.null)
                  (R := fun s => rb_equal_inv s ∧ s.locals.ca ≠ Ptr.null ∧ s.locals.cb ≠ Ptr.null)
                · -- cond(ca.value ≠ cb.value, ret0+throw, skip)
                  apply L1_hoare_condition
                  · -- true: values differ → ret=0, throw
                    intro s hpre
                    obtain ⟨⟨h_inv, h_ca_ne, h_cb_ne⟩, _⟩ := hpre
                    have h_mt := L1_modify_throw_result rb_equal_set_ret0 s
                    constructor
                    · exact h_mt.2
                    · intro r s' h_mem
                      rw [h_mt.1] at h_mem
                      have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                      subst hr; subst hs
                      unfold rb_equal_ret_bool
                      left; rw [rb_equal_set_ret0_locals_ret]
                  · -- false: values equal → skip
                    intro s hpre
                    obtain ⟨⟨h_inv, h_ca_ne, h_cb_ne⟩, _⟩ := hpre
                    constructor
                    · intro hf; exact hf
                    · intro r s' h_mem
                      have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                      match r with
                      | Except.ok () => subst hs; exact ⟨h_inv, h_ca_ne, h_cb_ne⟩
                      | Except.error () => exact absurd hr (by intro h; cases h)
                · -- seq(guard+ca_next, guard+cb_next)
                  apply L1_hoare_seq
                    (P := fun s => rb_equal_inv s ∧ s.locals.ca ≠ Ptr.null ∧ s.locals.cb ≠ Ptr.null)
                    (R := fun s => LinkedListValid s.globals.rawHeap s.locals.ca ∧
                                   LinkedListValid s.globals.rawHeap s.locals.cb ∧
                                   s.locals.cb ≠ Ptr.null)
                  · -- guard(heapPtrValid ca) >> ca := ca.next
                    intro s hpre
                    obtain ⟨⟨h_ca_ll, h_cb_ll⟩, h_ca_ne, h_cb_ne⟩ := hpre
                    have h_ca_valid := h_ca_ll.heapValid h_ca_ne
                    have h_ca_tail := h_ca_ll.tail h_ca_ne
                    have h_gm := L1_guard_modify_result
                      (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.ca)
                      rb_equal_set_ca_next s h_ca_valid
                    constructor
                    · exact h_gm.2
                    · intro r s' h_mem
                      rw [h_gm.1] at h_mem
                      have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                      subst hr; subst hs
                      refine ⟨?_, ?_, ?_⟩
                      · rw [rb_equal_set_ca_next_locals_ca, rb_equal_set_ca_next_globals]
                        exact h_ca_tail
                      · rw [rb_equal_set_ca_next_locals_cb, rb_equal_set_ca_next_globals]
                        exact h_cb_ll
                      · -- cb unchanged by ca_next step
                        rw [rb_equal_set_ca_next_locals_cb]; exact h_cb_ne
                  · -- guard(heapPtrValid cb) >> cb := cb.next
                    intro s hpre
                    obtain ⟨h_ca_ll, h_cb_ll, h_cb_ne⟩ := hpre
                    have h_cb_valid := h_cb_ll.heapValid h_cb_ne
                    have h_cb_tail := h_cb_ll.tail h_cb_ne
                    have h_gm := L1_guard_modify_result
                      (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cb)
                      rb_equal_set_cb_next s h_cb_valid
                    constructor
                    · exact h_gm.2
                    · intro r s' h_mem
                      rw [h_gm.1] at h_mem
                      have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                      subst hr; subst hs
                      unfold rb_equal_inv
                      exact ⟨by rw [rb_equal_set_cb_next_locals_ca, rb_equal_set_cb_next_globals]; exact h_ca_ll,
                             by rw [rb_equal_set_cb_next_locals_cb, rb_equal_set_cb_next_globals]; exact h_cb_tail⟩
            · -- while exit: invariant preserved
              intro s h_inv _
              exact h_inv
          · -- postloop: seq(cond(cb≠null, ret0+throw, skip), seq(ret1, throw))
            apply L1_hoare_seq (R := rb_equal_inv)
            · -- cond(cb ≠ null, ret0+throw, skip)
              apply L1_hoare_condition
              · -- true: cb ≠ null → ret=0, throw
                intro s hpre
                have h_mt := L1_modify_throw_result rb_equal_set_ret0 s
                constructor
                · exact h_mt.2
                · intro r s' h_mem
                  rw [h_mt.1] at h_mem
                  have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                  subst hr; subst hs
                  unfold rb_equal_ret_bool
                  left; rw [rb_equal_set_ret0_locals_ret]
              · -- false: cb = null → skip
                intro s hpre
                obtain ⟨h_inv, _⟩ := hpre
                constructor
                · intro hf; exact hf
                · intro r s' h_mem
                  have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                  match r with
                  | Except.ok () => subst hs; exact h_inv
                  | Except.error () => exact absurd hr (by intro h; cases h)
            · -- ret=1, throw
              intro s _
              have h_mt := L1_modify_throw_result rb_equal_set_ret1 s
              constructor
              · exact h_mt.2
              · intro r s' h_mem
                rw [h_mt.1] at h_mem
                have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                subst hr; subst hs
                unfold rb_equal_ret_bool
                right; rw [rb_equal_set_ret1_locals_ret]
  · -- catch handler: skip
    intro s h_ret
    constructor
    · intro hf; exact hf
    · intro r s' h_mem
      have ⟨hr, hs⟩ := Prod.mk.inj h_mem
      subst hr; subst hs
      intro _
      unfold rb_equal_ret_bool at h_ret
      constructor
      · exact h_ret
      · trivial
