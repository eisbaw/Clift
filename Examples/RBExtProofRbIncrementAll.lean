-- Proof for rb_increment_all_validHoare (split from RBExtProofsSorry for memory)
-- rb_increment_all: traverses linked list, increments each node's value by delta.
-- Pattern D (loop) with heap mutation per iteration.
-- Key: WellFormedList provides pairwise disjointness needed for heap frame reasoning.
import Examples.RBExtSpecs
set_option maxHeartbeats 25600000
set_option maxRecDepth 4096
open RingBufferExt

/-! # Loop invariant -/

private def rb_inc_all_inv (s : ProgramState) : Prop :=
  WellFormedList s.globals.rawHeap s.locals.cur

/-! # Named functions for each basic operation -/

-- modified := 0
private noncomputable def rb_inc_all_set_mod0 (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, (0 : UInt32),
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

-- cur := rb.head
private noncomputable def rb_inc_all_set_cur (s : ProgramState) : ProgramState :=
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

-- heap[cur].value += delta (modifies globals.rawHeap)
private noncomputable def rb_inc_all_heap_write (s : ProgramState) : ProgramState :=
  ⟨⟨heapUpdate s.globals.rawHeap s.locals.cur
      ({ hVal s.globals.rawHeap s.locals.cur with
        value := ((hVal s.globals.rawHeap s.locals.cur).value + s.locals.delta) })⟩,
    s.locals⟩

-- modified++
private noncomputable def rb_inc_all_inc_mod (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, (s.locals.modified + 1),
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

-- cur := cur.next (reads from current heap state)
private noncomputable def rb_inc_all_set_cur_next (s : ProgramState) : ProgramState :=
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

-- ret := modified
private noncomputable def rb_inc_all_set_ret (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.modified,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

/-! # Funext lemmas -/

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_inc_all_set_mod0_funext :
    (fun s : ProgramState => { s with locals := { s.locals with modified := (0 : UInt32) } }) =
      rb_inc_all_set_mod0 := by
  funext s; unfold rb_inc_all_set_mod0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_inc_all_set_cur_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      cur := (hVal s.globals.rawHeap s.locals.rb).head } }) = rb_inc_all_set_cur := by
  funext s; unfold rb_inc_all_set_cur; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_inc_all_heap_write_funext :
    (fun s : ProgramState => { s with globals := { s.globals with
      rawHeap := heapUpdate s.globals.rawHeap s.locals.cur
        ({ hVal s.globals.rawHeap s.locals.cur with
          value := ((hVal s.globals.rawHeap s.locals.cur).value + s.locals.delta) }) } }) =
      rb_inc_all_heap_write := by
  funext s; unfold rb_inc_all_heap_write; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_inc_all_inc_mod_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      modified := (s.locals.modified + 1) } }) = rb_inc_all_inc_mod := by
  funext s; unfold rb_inc_all_inc_mod; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_inc_all_set_cur_next_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      cur := (hVal s.globals.rawHeap s.locals.cur).next } }) = rb_inc_all_set_cur_next := by
  funext s; unfold rb_inc_all_set_cur_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_inc_all_set_ret_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      ret__val := s.locals.modified } }) = rb_inc_all_set_ret := by
  funext s; unfold rb_inc_all_set_ret; rfl

/-! # Projection lemmas -/

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_inc_all_set_mod0_globals (s : ProgramState) :
    (rb_inc_all_set_mod0 s).globals = s.globals := by unfold rb_inc_all_set_mod0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_inc_all_set_cur_globals (s : ProgramState) :
    (rb_inc_all_set_cur s).globals = s.globals := by unfold rb_inc_all_set_cur; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_inc_all_set_cur_locals_cur (s : ProgramState) :
    (rb_inc_all_set_cur s).locals.cur = (hVal s.globals.rawHeap s.locals.rb).head := by
  unfold rb_inc_all_set_cur; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_inc_all_heap_write_globals_rawHeap (s : ProgramState) :
    (rb_inc_all_heap_write s).globals.rawHeap =
      heapUpdate s.globals.rawHeap s.locals.cur
        ({ hVal s.globals.rawHeap s.locals.cur with
          value := ((hVal s.globals.rawHeap s.locals.cur).value + s.locals.delta) }) := by
  unfold rb_inc_all_heap_write; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_inc_all_heap_write_locals (s : ProgramState) :
    (rb_inc_all_heap_write s).locals = s.locals := by unfold rb_inc_all_heap_write; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_inc_all_heap_write_locals_cur (s : ProgramState) :
    (rb_inc_all_heap_write s).locals.cur = s.locals.cur := by unfold rb_inc_all_heap_write; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_inc_all_inc_mod_globals (s : ProgramState) :
    (rb_inc_all_inc_mod s).globals = s.globals := by unfold rb_inc_all_inc_mod; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_inc_all_inc_mod_locals_cur (s : ProgramState) :
    (rb_inc_all_inc_mod s).locals.cur = s.locals.cur := by unfold rb_inc_all_inc_mod; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_inc_all_set_cur_next_globals (s : ProgramState) :
    (rb_inc_all_set_cur_next s).globals = s.globals := by unfold rb_inc_all_set_cur_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_inc_all_set_cur_next_locals_cur (s : ProgramState) :
    (rb_inc_all_set_cur_next s).locals.cur = (hVal s.globals.rawHeap s.locals.cur).next := by
  unfold rb_inc_all_set_cur_next; rfl

/-! # Main theorem -/

set_option maxRecDepth 8192 in
set_option maxHeartbeats 51200000 in
attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem rb_increment_all_validHoare :
    rb_increment_all_spec.satisfiedBy RingBufferExt.l1_rb_increment_all_body := by
  unfold FuncSpec.satisfiedBy rb_increment_all_spec
  unfold RingBufferExt.l1_rb_increment_all_body
  simp only [rb_inc_all_set_mod0_funext, rb_inc_all_set_cur_funext,
    rb_inc_all_heap_write_funext, rb_inc_all_inc_mod_funext,
    rb_inc_all_set_cur_next_funext, rb_inc_all_set_ret_funext]
  -- Structure: catch (seq (mod0) (seq (guard rb; cur:=head) (seq (while ...) (seq (ret:=mod) throw)))) skip
  -- Postcondition is trivially true (each field = itself), so we only need non-failure.
  apply L1_hoare_catch (R := fun _ => True)
  · -- Body
    apply L1_hoare_seq (R := fun s =>
      heapPtrValid s.globals.rawHeap s.locals.rb ∧
      WellFormedList s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
    · -- modified := 0
      intro s hpre
      obtain ⟨h_rb, h_wf⟩ := hpre
      constructor
      · intro hf; exact hf
      · intro r s' h_mem
        have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
        rw [rb_inc_all_set_mod0_globals]
        exact ⟨h_rb, h_wf⟩
    · -- seq (guard rb; cur:=head) (seq (while ...) (seq (ret:=mod) throw))
      apply L1_hoare_seq (R := rb_inc_all_inv)
      · -- guard rb valid, then cur := rb.head
        intro s hpre
        obtain ⟨h_rb, h_wf⟩ := hpre
        have h_gm := L1_guard_modify_result
          (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
          rb_inc_all_set_cur s h_rb
        constructor
        · exact h_gm.2
        · intro r s' h_mem
          rw [h_gm.1] at h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem
          subst hr; subst hs
          unfold rb_inc_all_inv
          rw [rb_inc_all_set_cur_globals, rb_inc_all_set_cur_locals_cur]
          exact h_wf
      · -- seq (while ...) (seq (ret:=mod) throw)
        apply L1_hoare_seq (R := rb_inc_all_inv)
        · -- while loop
          apply L1_hoare_while_from_body
          · -- loop body: seq (guard; guard; heap_write) (seq (modified++) (guard cur; cur:=next))
            apply L1_hoare_seq
              (P := fun s => rb_inc_all_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
              (R := fun s => rb_inc_all_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
            · -- guard cur; guard cur; heap_write (heap[cur].value += delta)
              intro s hpre
              obtain ⟨h_inv, h_cond⟩ := hpre
              unfold rb_inc_all_inv at h_inv
              have h_ne : s.locals.cur ≠ Ptr.null := by
                simp only [decide_eq_true_eq] at h_cond; exact h_cond
              have h_valid := h_inv.headValid h_ne
              have h_ggm := L1_guard_guard_modify_result
                (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cur)
                (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cur)
                rb_inc_all_heap_write s h_valid h_valid
              constructor
              · exact h_ggm.2
              · intro r s' h_mem
                rw [h_ggm.1] at h_mem
                have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                subst hr; subst hs
                constructor
                · -- WellFormedList preserved through heapUpdate
                  unfold rb_inc_all_inv
                  rw [rb_inc_all_heap_write_globals_rawHeap, rb_inc_all_heap_write_locals_cur]
                  exact WellFormedList_heapUpdate_tail h_inv h_ne h_valid
                · -- cur ≠ null preserved (locals unchanged by heap write)
                  rw [rb_inc_all_heap_write_locals_cur]
                  exact h_cond
            · -- seq (modified++) (guard cur; cur := cur.next)
              apply L1_hoare_seq
                (P := fun s => rb_inc_all_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
                (R := fun s => rb_inc_all_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
              · -- modified++
                intro s hpre
                obtain ⟨⟨h_inv, h_cond⟩⟩ := hpre
                constructor
                · intro hf; exact hf
                · intro r s' h_mem
                  have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                  match r with
                  | Except.ok () =>
                    subst hs
                    constructor
                    · unfold rb_inc_all_inv at h_inv ⊢
                      rw [rb_inc_all_inc_mod_globals, rb_inc_all_inc_mod_locals_cur]
                      exact h_inv
                    · exact h_cond
                  | Except.error () =>
                    exact absurd hr (by intro h; cases h)
              · -- guard cur valid; cur := cur.next
                intro s hpre
                obtain ⟨⟨h_inv, h_cond⟩⟩ := hpre
                unfold rb_inc_all_inv at h_inv
                have h_ne : s.locals.cur ≠ Ptr.null := by
                  simp only [decide_eq_true_eq] at h_cond; exact h_cond
                have h_valid := h_inv.headValid h_ne
                have h_tail := h_inv.wf_tail h_ne
                have h_gm := L1_guard_modify_result
                  (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cur)
                  rb_inc_all_set_cur_next s h_valid
                constructor
                · exact h_gm.2
                · intro r s' h_mem
                  rw [h_gm.1] at h_mem
                  have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                  subst hr; subst hs
                  unfold rb_inc_all_inv
                  rw [rb_inc_all_set_cur_next_globals, rb_inc_all_set_cur_next_locals_cur]
                  exact h_tail
          · -- exit: while returns ok with invariant preserved
            intro s h_inv _
            exact h_inv
        · -- teardown: seq (ret:=modified) throw
          intro s h_inv
          have h_mt := L1_modify_throw_result rb_inc_all_set_ret s
          constructor
          · exact h_mt.2
          · intro r s' h_mem
            rw [h_mt.1] at h_mem
            have ⟨hr, hs⟩ := Prod.mk.inj h_mem
            subst hr; subst hs
            trivial
  · -- handler: skip → postcondition
    intro s _
    constructor
    · intro hf; exact hf
    · intro r s' h_mem
      have ⟨hr, hs⟩ := Prod.mk.inj h_mem
      subst hr; subst hs
      intro _
      exact ⟨rfl, rfl, rfl, rfl⟩
