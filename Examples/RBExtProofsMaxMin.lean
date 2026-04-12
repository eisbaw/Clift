-- Proven (sorry-free) validHoare proofs: rb_max and rb_min (loop + heap write).
-- Split from RBExtFuncSpecs.lean (task 0233).
--
-- WARNING: These proofs require >30GB RAM to build. They will OOM on machines
-- with <32GB RAM. The proofs are correct but expensive. Build on a CI server
-- with sufficient memory, or skip during local development.

import Examples.RBExtSpecs

set_option maxHeartbeats 12800000
set_option maxRecDepth 4096

open RingBufferExt

-- rb_max: step functions

private def rb_max_inv (s : ProgramState) : Prop :=
  LinkedListValid s.globals.rawHeap s.locals.cur ∧
  heapPtrValid s.globals.rawHeap s.locals.out_val

private def rb_max_catch_post (s : ProgramState) : Prop :=
  s.locals.ret__val = 0 ∧ heapPtrValid s.globals.rawHeap s.locals.out_val

private noncomputable def rb_max_set_maxval_head (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, (hVal s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head).value,
    s.locals.min_val, s.locals.modified, s.locals.n,
    s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

private noncomputable def rb_max_set_cur_head_next (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, (hVal s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head).next,
    s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified, s.locals.n,
    s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

private noncomputable def rb_max_update_maxval (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, (hVal s.globals.rawHeap s.locals.cur).value,
    s.locals.min_val, s.locals.modified, s.locals.n,
    s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

private noncomputable def rb_max_set_cur_next (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, (hVal s.globals.rawHeap s.locals.cur).next,
    s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified, s.locals.n,
    s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

private noncomputable def rb_max_heap_write (s : ProgramState) : ProgramState :=
  ⟨⟨heapUpdate s.globals.rawHeap s.locals.out_val s.locals.max_val⟩, s.locals⟩

private noncomputable def rb_max_set_ret0 (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified, s.locals.n,
    s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, (0 : UInt32),
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

-- rb_max: funext lemmas

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_max_set_maxval_head_funext :
    (fun s : ProgramState => { s with locals := { s.locals with max_val := (hVal s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head).value } }) = rb_max_set_maxval_head := by
  funext s; unfold rb_max_set_maxval_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_max_set_cur_head_next_funext :
    (fun s : ProgramState => { s with locals := { s.locals with cur := (hVal s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head).next } }) = rb_max_set_cur_head_next := by
  funext s; unfold rb_max_set_cur_head_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_max_update_maxval_funext :
    (fun s : ProgramState => { s with locals := { s.locals with max_val := (hVal s.globals.rawHeap s.locals.cur).value } }) = rb_max_update_maxval := by
  funext s; unfold rb_max_update_maxval; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_max_set_cur_next_funext :
    (fun s : ProgramState => { s with locals := { s.locals with cur := (hVal s.globals.rawHeap s.locals.cur).next } }) = rb_max_set_cur_next := by
  funext s; unfold rb_max_set_cur_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_max_heap_write_funext :
    (fun s : ProgramState => { s with globals := { rawHeap := heapUpdate s.globals.rawHeap s.locals.out_val s.locals.max_val } }) = rb_max_heap_write := by
  funext s; unfold rb_max_heap_write; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_max_set_ret0_funext :
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := (0 : UInt32) } }) = rb_max_set_ret0 := by
  funext s; unfold rb_max_set_ret0; rfl

-- rb_max: projection lemmas

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_max_set_maxval_head_globals (s : ProgramState) :
    (rb_max_set_maxval_head s).globals = s.globals := by unfold rb_max_set_maxval_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_max_set_maxval_head_locals_cur (s : ProgramState) :
    (rb_max_set_maxval_head s).locals.cur = s.locals.cur := by unfold rb_max_set_maxval_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_max_set_maxval_head_locals_out_val (s : ProgramState) :
    (rb_max_set_maxval_head s).locals.out_val = s.locals.out_val := by unfold rb_max_set_maxval_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_max_set_maxval_head_locals_rb (s : ProgramState) :
    (rb_max_set_maxval_head s).locals.rb = s.locals.rb := by unfold rb_max_set_maxval_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_max_set_cur_head_next_globals (s : ProgramState) :
    (rb_max_set_cur_head_next s).globals = s.globals := by unfold rb_max_set_cur_head_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_max_set_cur_head_next_locals_cur (s : ProgramState) :
    (rb_max_set_cur_head_next s).locals.cur = (hVal s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head).next := by unfold rb_max_set_cur_head_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_max_set_cur_head_next_locals_out_val (s : ProgramState) :
    (rb_max_set_cur_head_next s).locals.out_val = s.locals.out_val := by unfold rb_max_set_cur_head_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_max_update_maxval_globals (s : ProgramState) :
    (rb_max_update_maxval s).globals = s.globals := by unfold rb_max_update_maxval; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_max_update_maxval_locals_cur (s : ProgramState) :
    (rb_max_update_maxval s).locals.cur = s.locals.cur := by unfold rb_max_update_maxval; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_max_update_maxval_locals_out_val (s : ProgramState) :
    (rb_max_update_maxval s).locals.out_val = s.locals.out_val := by unfold rb_max_update_maxval; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_max_set_cur_next_globals (s : ProgramState) :
    (rb_max_set_cur_next s).globals = s.globals := by unfold rb_max_set_cur_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_max_set_cur_next_locals_cur (s : ProgramState) :
    (rb_max_set_cur_next s).locals.cur = (hVal s.globals.rawHeap s.locals.cur).next := by unfold rb_max_set_cur_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_max_set_cur_next_locals_out_val (s : ProgramState) :
    (rb_max_set_cur_next s).locals.out_val = s.locals.out_val := by unfold rb_max_set_cur_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_max_heap_write_globals_rawHeap (s : ProgramState) :
    (rb_max_heap_write s).globals.rawHeap = heapUpdate s.globals.rawHeap s.locals.out_val s.locals.max_val := by unfold rb_max_heap_write; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_max_heap_write_locals_out_val (s : ProgramState) :
    (rb_max_heap_write s).locals.out_val = s.locals.out_val := by unfold rb_max_heap_write; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_max_set_ret0_globals (s : ProgramState) :
    (rb_max_set_ret0 s).globals = s.globals := by unfold rb_max_set_ret0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_max_set_ret0_locals_ret (s : ProgramState) :
    (rb_max_set_ret0 s).locals.ret__val = 0 := by unfold rb_max_set_ret0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_max_set_ret0_locals_out_val (s : ProgramState) :
    (rb_max_set_ret0 s).locals.out_val = s.locals.out_val := by unfold rb_max_set_ret0; rfl

-- rb_max: the main proof
set_option maxRecDepth 8192 in
set_option maxHeartbeats 25600000 in
attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem rb_max_validHoare :
    rb_max_spec.satisfiedBy RingBufferExt.l1_rb_max_body := by
  unfold FuncSpec.satisfiedBy rb_max_spec
  unfold RingBufferExt.l1_rb_max_body
  simp only [rb_max_set_maxval_head_funext, rb_max_set_cur_head_next_funext,
    rb_max_update_maxval_funext, rb_max_set_cur_next_funext,
    rb_max_heap_write_funext, rb_max_set_ret0_funext]
  apply L1_hoare_catch (R := rb_max_catch_post)
  · -- catch body: seq (cond ...) (seq ...)
    apply L1_hoare_seq (R := fun s =>
      heapPtrValid s.globals.rawHeap s.locals.rb ∧
      heapPtrValid s.globals.rawHeap s.locals.out_val ∧
      (hVal s.globals.rawHeap s.locals.rb).head ≠ Ptr.null ∧
      heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head ∧
      LinkedListValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
    · -- cond (head == null): since head ≠ null from pre, takes false branch (skip)
      apply L1_hoare_condition
      · -- true branch: ret:=1; throw (dead code, head ≠ null)
        intro s hpre
        obtain ⟨⟨h_rb, h_out, h_nn, h_head, h_ll⟩, h_cond⟩ := hpre
        simp only [decide_eq_true_eq] at h_cond
        exact absurd h_cond h_nn
      · -- false branch: skip
        intro s hpre
        obtain ⟨⟨h_rb, h_out, h_nn, h_head, h_ll⟩, _⟩ := hpre
        constructor
        · intro hf; exact hf
        · intro r s' h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem
          match r with
          | Except.ok () => subst hs; exact ⟨h_rb, h_out, h_nn, h_head, h_ll⟩
          | Except.error () => exact absurd hr (by intro h; cases h)
    · -- seq (guard+modify max_val) (seq (guard+modify cur) (seq while (seq heap_write (seq ret:=0 throw))))
      apply L1_hoare_seq (R := fun s =>
        heapPtrValid s.globals.rawHeap s.locals.out_val ∧
        (hVal s.globals.rawHeap s.locals.rb).head ≠ Ptr.null ∧
        heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head ∧
        LinkedListValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
      · -- guard head_valid; modify max_val := head->value
        intro s hpre
        obtain ⟨h_rb, h_out, h_nn, h_head, h_ll⟩ := hpre
        have h_gm := L1_guard_modify_result
          (fun s : ProgramState => heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
          rb_max_set_maxval_head s h_head
        constructor
        · exact h_gm.2
        · intro r s' h_mem
          rw [h_gm.1] at h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem
          subst hr; subst hs
          rw [rb_max_set_maxval_head_globals, rb_max_set_maxval_head_locals_out_val,
              rb_max_set_maxval_head_locals_rb]
          exact ⟨h_out, h_nn, h_head, h_ll⟩
      · -- seq (guard+modify cur:=head->next) (seq while ...)
        apply L1_hoare_seq (R := rb_max_inv)
        · -- guard head_valid; modify cur := head->next
          intro s hpre
          obtain ⟨h_out, h_nn, h_head, h_ll⟩ := hpre
          have h_gm := L1_guard_modify_result
            (fun s : ProgramState => heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
            rb_max_set_cur_head_next s h_head
          constructor
          · exact h_gm.2
          · intro r s' h_mem
            rw [h_gm.1] at h_mem
            have ⟨hr, hs⟩ := Prod.mk.inj h_mem
            subst hr; subst hs
            unfold rb_max_inv
            rw [rb_max_set_cur_head_next_globals, rb_max_set_cur_head_next_locals_cur,
                rb_max_set_cur_head_next_locals_out_val]
            exact ⟨h_ll.tail h_nn, h_out⟩
        · -- seq while (seq heap_write (seq ret:=0 throw))
          apply L1_hoare_seq (R := fun s =>
            rb_max_inv s)
          · -- while loop
            apply L1_hoare_while_from_body
            · -- loop body: seq (cond ...) (seq (guard cur) (modify cur:=cur->next))
              apply L1_hoare_seq
                (P := fun s => rb_max_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
                (R := fun s => rb_max_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
              · -- cond (cur->value > max_val): true updates max_val, false skips
                apply L1_hoare_condition
                · -- true: guard cur; modify max_val := cur->value
                  intro s hpre
                  obtain ⟨⟨⟨h_ll, h_out⟩, h_cond⟩, _⟩ := hpre
                  have h_ne : s.locals.cur ≠ Ptr.null := by
                    simp only [decide_eq_true_eq] at h_cond; exact h_cond
                  have h_cur_valid := h_ll.heapValid h_ne
                  have h_gm := L1_guard_modify_result
                    (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cur)
                    rb_max_update_maxval s h_cur_valid
                  constructor
                  · exact h_gm.2
                  · intro r s' h_mem
                    rw [h_gm.1] at h_mem
                    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                    match r with
                    | Except.ok () =>
                      subst hs
                      unfold rb_max_inv
                      rw [rb_max_update_maxval_globals, rb_max_update_maxval_locals_cur,
                          rb_max_update_maxval_locals_out_val]
                      exact ⟨⟨h_ll, h_out⟩, h_cond⟩
                    | Except.error () =>
                      exact absurd hr (by intro h; cases h)
                · -- false: skip
                  intro s hpre
                  obtain ⟨⟨h_inv, h_cond⟩, _⟩ := hpre
                  constructor
                  · intro hf; exact hf
                  · intro r s' h_mem
                    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                    match r with
                    | Except.ok () => subst hs; exact ⟨h_inv, h_cond⟩
                    | Except.error () => exact absurd hr (by intro h; cases h)
              · -- guard cur valid; modify cur := cur->next
                intro s hpre
                obtain ⟨⟨h_ll, h_out⟩, h_cond⟩ := hpre
                unfold rb_max_inv at h_ll h_out
                have h_ne : s.locals.cur ≠ Ptr.null := by
                  simp only [decide_eq_true_eq] at h_cond; exact h_cond
                have h_valid := h_ll.heapValid h_ne
                have h_tail := h_ll.tail h_ne
                have h_gm := L1_guard_modify_result
                  (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cur)
                  rb_max_set_cur_next s h_valid
                constructor
                · exact h_gm.2
                · intro r s' h_mem
                  rw [h_gm.1] at h_mem
                  have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                  subst hr; subst hs
                  unfold rb_max_inv
                  rw [rb_max_set_cur_next_globals, rb_max_set_cur_next_locals_cur,
                      rb_max_set_cur_next_locals_out_val]
                  exact ⟨h_tail, h_out⟩
            · -- exit: while ok → inv preserved
              intro s h_inv _
              exact h_inv
          · -- teardown: seq (guard+modify heap) (seq (modify ret:=0) throw)
            intro s h_inv
            obtain ⟨_, h_out⟩ := h_inv
            have h_gm := L1_guard_modify_result
              (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.out_val)
              rb_max_heap_write s h_out
            have h_mt := L1_modify_throw_result rb_max_set_ret0 (rb_max_heap_write s)
            have h_sok := L1_seq_singleton_ok h_gm.1 h_gm.2
              (m₂ := L1.seq (L1.modify rb_max_set_ret0) L1.throw)
            constructor
            · intro hf; exact h_mt.2 (h_sok.2.mp hf)
            · intro r s' h_mem
              rw [h_sok.1, h_mt.1] at h_mem
              have ⟨hr, hs⟩ := Prod.mk.inj h_mem
              subst hr; subst hs
              unfold rb_max_catch_post
              exact ⟨rb_max_set_ret0_locals_ret (rb_max_heap_write s),
                by rw [rb_max_set_ret0_globals, rb_max_set_ret0_locals_out_val,
                    rb_max_heap_write_globals_rawHeap, rb_max_heap_write_locals_out_val]
                   exact heapUpdate_preserves_heapPtrValid _ _ _ _ h_out⟩
  · -- handler: skip
    intro s h_catch
    constructor
    · intro hf; exact hf
    · intro r s' h_mem
      have ⟨hr, hs⟩ := Prod.mk.inj h_mem
      subst hr; subst hs
      intro _
      obtain ⟨h_ret, h_out⟩ := h_catch
      exact ⟨h_ret, h_out, rfl⟩


-- rb_min: loop + heap write
-- The original rb_min_spec (in RingBufferExtProof.lean) has a precondition too weak to prove
-- validHoare (missing LinkedListValid for loop guards). We define a strengthened spec here.
def rb_min_spec_ext : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.rb ∧
    heapPtrValid s.globals.rawHeap s.locals.out_val ∧
    (hVal s.globals.rawHeap s.locals.rb).head ≠ Ptr.null ∧
    heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head ∧
    LinkedListValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head
  post := fun r s =>
    r = Except.ok () →
    s.locals.ret__val = 0

-- rb_min: step functions

private def rb_min_inv (s : ProgramState) : Prop :=
  LinkedListValid s.globals.rawHeap s.locals.cur ∧
  heapPtrValid s.globals.rawHeap s.locals.out_val

private noncomputable def rb_min_set_minval_head (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val,
    (hVal s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head).value,
    s.locals.modified, s.locals.n,
    s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

private noncomputable def rb_min_set_cur_head_next (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, (hVal s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head).next,
    s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified, s.locals.n,
    s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

private noncomputable def rb_min_update_minval (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val,
    (hVal s.globals.rawHeap s.locals.cur).value,
    s.locals.modified, s.locals.n,
    s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

private noncomputable def rb_min_set_cur_next (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, (hVal s.globals.rawHeap s.locals.cur).next,
    s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified, s.locals.n,
    s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

private noncomputable def rb_min_heap_write (s : ProgramState) : ProgramState :=
  ⟨⟨heapUpdate s.globals.rawHeap s.locals.out_val s.locals.min_val⟩, s.locals⟩

private noncomputable def rb_min_set_ret0 (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified, s.locals.n,
    s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, (0 : UInt32),
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

-- rb_min: funext lemmas

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_min_set_minval_head_funext :
    (fun s : ProgramState => { s with locals := { s.locals with min_val := (hVal s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head).value } }) = rb_min_set_minval_head := by
  funext s; unfold rb_min_set_minval_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_min_set_cur_head_next_funext :
    (fun s : ProgramState => { s with locals := { s.locals with cur := (hVal s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head).next } }) = rb_min_set_cur_head_next := by
  funext s; unfold rb_min_set_cur_head_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_min_update_minval_funext :
    (fun s : ProgramState => { s with locals := { s.locals with min_val := (hVal s.globals.rawHeap s.locals.cur).value } }) = rb_min_update_minval := by
  funext s; unfold rb_min_update_minval; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_min_set_cur_next_funext :
    (fun s : ProgramState => { s with locals := { s.locals with cur := (hVal s.globals.rawHeap s.locals.cur).next } }) = rb_min_set_cur_next := by
  funext s; unfold rb_min_set_cur_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_min_heap_write_funext :
    (fun s : ProgramState => { s with globals := { rawHeap := heapUpdate s.globals.rawHeap s.locals.out_val s.locals.min_val } }) = rb_min_heap_write := by
  funext s; unfold rb_min_heap_write; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_min_set_ret0_funext :
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := (0 : UInt32) } }) = rb_min_set_ret0 := by
  funext s; unfold rb_min_set_ret0; rfl

-- rb_min: projection lemmas

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_min_set_minval_head_globals (s : ProgramState) :
    (rb_min_set_minval_head s).globals = s.globals := by unfold rb_min_set_minval_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_min_set_minval_head_locals_cur (s : ProgramState) :
    (rb_min_set_minval_head s).locals.cur = s.locals.cur := by unfold rb_min_set_minval_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_min_set_minval_head_locals_out_val (s : ProgramState) :
    (rb_min_set_minval_head s).locals.out_val = s.locals.out_val := by unfold rb_min_set_minval_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_min_set_minval_head_locals_rb (s : ProgramState) :
    (rb_min_set_minval_head s).locals.rb = s.locals.rb := by unfold rb_min_set_minval_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_min_set_cur_head_next_globals (s : ProgramState) :
    (rb_min_set_cur_head_next s).globals = s.globals := by unfold rb_min_set_cur_head_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_min_set_cur_head_next_locals_cur (s : ProgramState) :
    (rb_min_set_cur_head_next s).locals.cur = (hVal s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head).next := by unfold rb_min_set_cur_head_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_min_set_cur_head_next_locals_out_val (s : ProgramState) :
    (rb_min_set_cur_head_next s).locals.out_val = s.locals.out_val := by unfold rb_min_set_cur_head_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_min_update_minval_globals (s : ProgramState) :
    (rb_min_update_minval s).globals = s.globals := by unfold rb_min_update_minval; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_min_update_minval_locals_cur (s : ProgramState) :
    (rb_min_update_minval s).locals.cur = s.locals.cur := by unfold rb_min_update_minval; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_min_update_minval_locals_out_val (s : ProgramState) :
    (rb_min_update_minval s).locals.out_val = s.locals.out_val := by unfold rb_min_update_minval; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_min_set_cur_next_globals (s : ProgramState) :
    (rb_min_set_cur_next s).globals = s.globals := by unfold rb_min_set_cur_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_min_set_cur_next_locals_cur (s : ProgramState) :
    (rb_min_set_cur_next s).locals.cur = (hVal s.globals.rawHeap s.locals.cur).next := by unfold rb_min_set_cur_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_min_set_cur_next_locals_out_val (s : ProgramState) :
    (rb_min_set_cur_next s).locals.out_val = s.locals.out_val := by unfold rb_min_set_cur_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_min_set_ret0_globals (s : ProgramState) :
    (rb_min_set_ret0 s).globals = s.globals := by unfold rb_min_set_ret0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_min_set_ret0_locals_ret (s : ProgramState) :
    (rb_min_set_ret0 s).locals.ret__val = 0 := by unfold rb_min_set_ret0; rfl

-- rb_min: the main proof
set_option maxRecDepth 8192 in
set_option maxHeartbeats 25600000 in
attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem rb_min_validHoare :
    rb_min_spec_ext.satisfiedBy RingBufferExt.l1_rb_min_body := by
  unfold FuncSpec.satisfiedBy rb_min_spec_ext
  unfold RingBufferExt.l1_rb_min_body
  simp only [rb_min_set_minval_head_funext, rb_min_set_cur_head_next_funext,
    rb_min_update_minval_funext, rb_min_set_cur_next_funext,
    rb_min_heap_write_funext, rb_min_set_ret0_funext]
  apply L1_hoare_catch (R := fun s => s.locals.ret__val = 0)
  · -- catch body
    apply L1_hoare_seq (R := fun s =>
      heapPtrValid s.globals.rawHeap s.locals.rb ∧
      heapPtrValid s.globals.rawHeap s.locals.out_val ∧
      (hVal s.globals.rawHeap s.locals.rb).head ≠ Ptr.null ∧
      heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head ∧
      LinkedListValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
    · -- cond (head == null): dead branch since head ≠ null
      apply L1_hoare_condition
      · -- true: ret:=1; throw (dead code)
        intro s hpre
        obtain ⟨⟨h_rb, h_out, h_nn, h_head, h_ll⟩, h_cond⟩ := hpre
        simp only [decide_eq_true_eq] at h_cond
        exact absurd h_cond h_nn
      · -- false: skip
        intro s hpre
        obtain ⟨⟨h_rb, h_out, h_nn, h_head, h_ll⟩, _⟩ := hpre
        constructor
        · intro hf; exact hf
        · intro r s' h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem
          match r with
          | Except.ok () => subst hs; exact ⟨h_rb, h_out, h_nn, h_head, h_ll⟩
          | Except.error () => exact absurd hr (by intro h; cases h)
    · -- seq (guard+modify min_val) (seq (guard+modify cur) (seq while (seq heap_write (seq ret:=0 throw))))
      apply L1_hoare_seq (R := fun s =>
        heapPtrValid s.globals.rawHeap s.locals.out_val ∧
        (hVal s.globals.rawHeap s.locals.rb).head ≠ Ptr.null ∧
        heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head ∧
        LinkedListValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
      · -- guard head_valid; modify min_val := head->value
        intro s hpre
        obtain ⟨h_rb, h_out, h_nn, h_head, h_ll⟩ := hpre
        have h_gm := L1_guard_modify_result
          (fun s : ProgramState => heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
          rb_min_set_minval_head s h_head
        constructor
        · exact h_gm.2
        · intro r s' h_mem
          rw [h_gm.1] at h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem
          subst hr; subst hs
          rw [rb_min_set_minval_head_globals, rb_min_set_minval_head_locals_out_val,
              rb_min_set_minval_head_locals_rb]
          exact ⟨h_out, h_nn, h_head, h_ll⟩
      · -- seq (guard+modify cur:=head->next) (seq while ...)
        apply L1_hoare_seq (R := rb_min_inv)
        · -- guard head_valid; modify cur := head->next
          intro s hpre
          obtain ⟨h_out, h_nn, h_head, h_ll⟩ := hpre
          have h_gm := L1_guard_modify_result
            (fun s : ProgramState => heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
            rb_min_set_cur_head_next s h_head
          constructor
          · exact h_gm.2
          · intro r s' h_mem
            rw [h_gm.1] at h_mem
            have ⟨hr, hs⟩ := Prod.mk.inj h_mem
            subst hr; subst hs
            unfold rb_min_inv
            rw [rb_min_set_cur_head_next_globals, rb_min_set_cur_head_next_locals_cur,
                rb_min_set_cur_head_next_locals_out_val]
            exact ⟨h_ll.tail h_nn, h_out⟩
        · -- seq while (seq heap_write (seq ret:=0 throw))
          apply L1_hoare_seq (R := rb_min_inv)
          · -- while loop
            apply L1_hoare_while_from_body
            · -- loop body
              apply L1_hoare_seq
                (P := fun s => rb_min_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
                (R := fun s => rb_min_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
              · -- cond (cur->value < min_val)
                apply L1_hoare_condition
                · -- true: guard cur; modify min_val := cur->value
                  intro s hpre
                  obtain ⟨⟨⟨h_ll, h_out⟩, h_cond⟩, _⟩ := hpre
                  have h_ne : s.locals.cur ≠ Ptr.null := by
                    simp only [decide_eq_true_eq] at h_cond; exact h_cond
                  have h_cur_valid := h_ll.heapValid h_ne
                  have h_gm := L1_guard_modify_result
                    (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cur)
                    rb_min_update_minval s h_cur_valid
                  constructor
                  · exact h_gm.2
                  · intro r s' h_mem
                    rw [h_gm.1] at h_mem
                    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                    match r with
                    | Except.ok () =>
                      subst hs
                      unfold rb_min_inv
                      rw [rb_min_update_minval_globals, rb_min_update_minval_locals_cur,
                          rb_min_update_minval_locals_out_val]
                      exact ⟨⟨h_ll, h_out⟩, h_cond⟩
                    | Except.error () =>
                      exact absurd hr (by intro h; cases h)
                · -- false: skip
                  intro s hpre
                  obtain ⟨⟨h_inv, h_cond⟩, _⟩ := hpre
                  constructor
                  · intro hf; exact hf
                  · intro r s' h_mem
                    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                    match r with
                    | Except.ok () => subst hs; exact ⟨h_inv, h_cond⟩
                    | Except.error () => exact absurd hr (by intro h; cases h)
              · -- guard cur valid; modify cur := cur->next
                intro s hpre
                obtain ⟨⟨h_ll, h_out⟩, h_cond⟩ := hpre
                unfold rb_min_inv at h_ll h_out
                have h_ne : s.locals.cur ≠ Ptr.null := by
                  simp only [decide_eq_true_eq] at h_cond; exact h_cond
                have h_valid := h_ll.heapValid h_ne
                have h_tail := h_ll.tail h_ne
                have h_gm := L1_guard_modify_result
                  (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cur)
                  rb_min_set_cur_next s h_valid
                constructor
                · exact h_gm.2
                · intro r s' h_mem
                  rw [h_gm.1] at h_mem
                  have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                  subst hr; subst hs
                  unfold rb_min_inv
                  rw [rb_min_set_cur_next_globals, rb_min_set_cur_next_locals_cur,
                      rb_min_set_cur_next_locals_out_val]
                  exact ⟨h_tail, h_out⟩
            · -- exit: inv preserved
              intro s h_inv _
              exact h_inv
          · -- teardown: seq (guard+modify heap) (seq (modify ret:=0) throw)
            intro s h_inv
            obtain ⟨_, h_out⟩ := h_inv
            have h_gm := L1_guard_modify_result
              (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.out_val)
              rb_min_heap_write s h_out
            have h_mt := L1_modify_throw_result rb_min_set_ret0 (rb_min_heap_write s)
            have h_sok := L1_seq_singleton_ok h_gm.1 h_gm.2
              (m₂ := L1.seq (L1.modify rb_min_set_ret0) L1.throw)
            constructor
            · intro hf; exact h_mt.2 (h_sok.2.mp hf)
            · intro r s' h_mem
              rw [h_sok.1, h_mt.1] at h_mem
              have ⟨hr, hs⟩ := Prod.mk.inj h_mem
              subst hr; subst hs
              exact rb_min_set_ret0_locals_ret (rb_min_heap_write s)
  · -- handler: skip
    intro s h_catch
    constructor
    · intro hf; exact hf
    · intro r s' h_mem
      have ⟨hr, hs⟩ := Prod.mk.inj h_mem
      subst hr; subst hs
      intro _
      exact h_catch

