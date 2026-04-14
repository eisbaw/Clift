-- Proven (sorry-free) validHoare proofs: rb_count_above and rb_count_at_or_below.
-- Split from RBExtFuncSpecs.lean (task 0233).

import Examples.RBExtSpecs

set_option maxHeartbeats 12800000
set_option maxRecDepth 4096

open RingBufferExt

-- rb_count_above: loop
private def rb_count_above_inv (s : ProgramState) : Prop :=
  LinkedListValid s.globals.rawHeap s.locals.cur

private noncomputable def rb_count_above_set_count0 (s : ProgramState) : ProgramState :=
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

private noncomputable def rb_count_above_set_cur (s : ProgramState) : ProgramState :=
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

private noncomputable def rb_count_above_inc_count (s : ProgramState) : ProgramState :=
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

private noncomputable def rb_count_above_set_cur_next (s : ProgramState) : ProgramState :=
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

private noncomputable def rb_count_above_set_ret_count (s : ProgramState) : ProgramState :=
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

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_count_above_set_count0_funext :
    (fun s : ProgramState => { s with locals := { s.locals with count := (0 : UInt32) } }) = rb_count_above_set_count0 := by
  funext s; unfold rb_count_above_set_count0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_count_above_set_cur_funext :
    (fun s : ProgramState => { s with locals := { s.locals with cur := (hVal s.globals.rawHeap s.locals.rb).head } }) = rb_count_above_set_cur := by
  funext s; unfold rb_count_above_set_cur; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_count_above_inc_count_funext :
    (fun s : ProgramState => { s with locals := { s.locals with count := s.locals.count + 1 } }) = rb_count_above_inc_count := by
  funext s; unfold rb_count_above_inc_count; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_count_above_set_cur_next_funext :
    (fun s : ProgramState => { s with locals := { s.locals with cur := (hVal s.globals.rawHeap s.locals.cur).next } }) = rb_count_above_set_cur_next := by
  funext s; unfold rb_count_above_set_cur_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_count_above_set_ret_count_funext :
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := s.locals.count } }) = rb_count_above_set_ret_count := by
  funext s; unfold rb_count_above_set_ret_count; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_count_above_set_cur_globals (s : ProgramState) :
    (rb_count_above_set_cur s).globals = s.globals := by unfold rb_count_above_set_cur; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_count_above_set_cur_locals_eq (s : ProgramState) :
    (rb_count_above_set_cur s).locals = ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca,
      s.locals.cap, s.locals.cb, s.locals.count, (hVal s.globals.rawHeap s.locals.rb).head,
      s.locals.current_count, s.locals.delta, s.locals.dst, s.locals.filled,
      s.locals.front, s.locals.idx, s.locals.iter, s.locals.max_drain,
      s.locals.max_val, s.locals.min_val, s.locals.modified, s.locals.n,
      s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
      s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
      s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
      s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
      s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
      s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
      s.locals.transferred, s.locals.val⟩ := by unfold rb_count_above_set_cur; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_count_above_set_cur_locals_cur (s : ProgramState) :
    (rb_count_above_set_cur s).locals.cur = (hVal s.globals.rawHeap s.locals.rb).head := by
  rw [rb_count_above_set_cur_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_count_above_set_cur_next_globals (s : ProgramState) :
    (rb_count_above_set_cur_next s).globals = s.globals := by unfold rb_count_above_set_cur_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_count_above_set_cur_next_locals_eq (s : ProgramState) :
    (rb_count_above_set_cur_next s).locals = ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca,
      s.locals.cap, s.locals.cb, s.locals.count, (hVal s.globals.rawHeap s.locals.cur).next,
      s.locals.current_count, s.locals.delta, s.locals.dst, s.locals.filled,
      s.locals.front, s.locals.idx, s.locals.iter, s.locals.max_drain,
      s.locals.max_val, s.locals.min_val, s.locals.modified, s.locals.n,
      s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
      s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
      s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
      s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
      s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
      s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
      s.locals.transferred, s.locals.val⟩ := by unfold rb_count_above_set_cur_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_count_above_set_cur_next_locals_cur (s : ProgramState) :
    (rb_count_above_set_cur_next s).locals.cur = (hVal s.globals.rawHeap s.locals.cur).next := by
  rw [rb_count_above_set_cur_next_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_count_above_inc_count_globals (s : ProgramState) :
    (rb_count_above_inc_count s).globals = s.globals := by unfold rb_count_above_inc_count; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_count_above_inc_count_locals_eq (s : ProgramState) :
    (rb_count_above_inc_count s).locals = ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca,
      s.locals.cap, s.locals.cb, s.locals.count + 1, s.locals.cur, s.locals.current_count,
      s.locals.delta, s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx,
      s.locals.iter, s.locals.max_drain, s.locals.max_val, s.locals.min_val,
      s.locals.modified, s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt,
      s.locals.old_head, s.locals.old_val, s.locals.out_val, s.locals.pop_ok,
      s.locals.pop_result, s.locals.prev, s.locals.push_ok, s.locals.push_result,
      s.locals.rb, s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
      s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
      s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
      s.locals.transferred, s.locals.val⟩ := by unfold rb_count_above_inc_count; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_count_above_inc_count_locals_cur (s : ProgramState) :
    (rb_count_above_inc_count s).locals.cur = s.locals.cur := by
  rw [rb_count_above_inc_count_locals_eq]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 25600000 in
attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem rb_count_above_validHoare :
    rb_count_above_spec.satisfiedBy RingBufferExt.l1_rb_count_above_body := by
  unfold FuncSpec.satisfiedBy rb_count_above_spec
  apply validHoare_weaken_trivial_post (fun _ _ => fun _ => rfl)
  unfold RingBufferExt.l1_rb_count_above_body
  simp only [rb_count_above_set_count0_funext, rb_count_above_set_cur_funext,
    rb_count_above_inc_count_funext, rb_count_above_set_cur_next_funext,
    rb_count_above_set_ret_count_funext]
  apply L1_hoare_catch (R := fun _ => True)
  · apply L1_hoare_seq (R := fun s =>
      heapPtrValid s.globals.rawHeap s.locals.rb ∧
      LinkedListValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
    · -- modify count=0
      intro s₀ hpre
      constructor
      · intro h; exact h
      · intro r s₁ h_mem
        have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
        exact hpre
    · apply L1_hoare_seq (R := rb_count_above_inv)
      · -- setup: guard rb valid, then cur := rb.head
        intro s hpre
        obtain ⟨h_rb, h_ll⟩ := hpre
        have h_gm := L1_guard_modify_result
          (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
          rb_count_above_set_cur s h_rb
        constructor
        · exact h_gm.2
        · intro r s' h_mem
          rw [h_gm.1] at h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem
          subst hr; subst hs
          unfold rb_count_above_inv
          rw [rb_count_above_set_cur_globals, rb_count_above_set_cur_locals_cur]
          exact h_ll
      · -- rest: while + teardown
        apply L1_hoare_seq (R := fun _ => True)
        · -- while loop
          apply L1_hoare_while_from_body
          · -- loop body
            apply L1_hoare_seq
              (P := fun s => rb_count_above_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
              (R := fun s => rb_count_above_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
            · -- if cur->value > threshold then count++ else skip
              apply L1_hoare_condition
              · intro s hpre
                obtain ⟨⟨h_inv, h_cond⟩, h_match⟩ := hpre
                constructor
                · intro hf; exact hf
                · intro r s' h_mem
                  have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                  match r with
                  | Except.ok () =>
                    subst hs
                    unfold rb_count_above_inv
                    rw [rb_count_above_inc_count_globals, rb_count_above_inc_count_locals_cur]
                    exact ⟨h_inv, h_cond⟩
                  | Except.error () =>
                    exact absurd hr (by intro h; cases h)
              · intro s hpre
                obtain ⟨⟨h_inv, h_cond⟩, h_nomatch⟩ := hpre
                constructor
                · intro hf; exact hf
                · intro r s' h_mem
                  have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                  match r with
                  | Except.ok () =>
                    subst hs
                    exact ⟨h_inv, h_cond⟩
                  | Except.error () =>
                    exact absurd hr (by intro h; cases h)
            · -- guard cur valid, then cur := cur->next
              intro s hpre
              obtain ⟨h_inv, h_cond⟩ := hpre
              unfold rb_count_above_inv at h_inv
              have h_ne : s.locals.cur ≠ Ptr.null := by
                simp only [decide_eq_true_eq] at h_cond
                exact h_cond
              have h_valid := h_inv.heapValid h_ne
              have h_tail := h_inv.tail h_ne
              have h_gm := L1_guard_modify_result
                (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cur)
                rb_count_above_set_cur_next s h_valid
              constructor
              · exact h_gm.2
              · intro r s' h_mem
                rw [h_gm.1] at h_mem
                have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                subst hr; subst hs
                unfold rb_count_above_inv
                rw [rb_count_above_set_cur_next_globals, rb_count_above_set_cur_next_locals_cur]
                exact h_tail
          · -- exit condition: while returns ok with invariant
            intro s h_inv _
            trivial
        · -- teardown: ret := count; throw
          intro s h_inv
          have h_mt := L1_modify_throw_result rb_count_above_set_ret_count s
          constructor
          · exact h_mt.2
          · intro r s' h_mem
            rw [h_mt.1] at h_mem
            have ⟨hr, hs⟩ := Prod.mk.inj h_mem
            subst hr; subst hs
            trivial
  · -- handler: skip
    intro _ _
    exact ⟨not_false, fun _ _ _ => trivial⟩


-- rb_count_at_or_below: loop
theorem rb_count_at_or_below_validHoare :
    rb_count_at_or_below_spec.satisfiedBy RingBufferExt.l1_rb_count_at_or_below_body := by
  unfold FuncSpec.satisfiedBy rb_count_at_or_below_spec
  apply validHoare_weaken_trivial_post (fun _ _ => fun _ => rfl)
  unfold RingBufferExt.l1_rb_count_at_or_below_body
  simp only [rb_count_above_set_count0_funext, rb_count_above_set_cur_funext,
    rb_count_above_inc_count_funext, rb_count_above_set_cur_next_funext,
    rb_count_above_set_ret_count_funext]
  apply L1_hoare_catch (R := fun _ => True)
  · apply L1_hoare_seq (R := fun s =>
      heapPtrValid s.globals.rawHeap s.locals.rb ∧
      LinkedListValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
    · -- modify count=0
      intro s₀ hpre
      constructor
      · intro h; exact h
      · intro r s₁ h_mem
        have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
        exact hpre
    · apply L1_hoare_seq (R := rb_count_above_inv)
      · -- setup: guard rb valid, then cur := rb.head
        intro s hpre
        obtain ⟨h_rb, h_ll⟩ := hpre
        have h_gm := L1_guard_modify_result
          (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
          rb_count_above_set_cur s h_rb
        constructor
        · exact h_gm.2
        · intro r s' h_mem
          rw [h_gm.1] at h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem
          subst hr; subst hs
          unfold rb_count_above_inv
          rw [rb_count_above_set_cur_globals, rb_count_above_set_cur_locals_cur]
          exact h_ll
      · -- rest: while + teardown
        apply L1_hoare_seq (R := fun _ => True)
        · -- while loop
          apply L1_hoare_while_from_body
          · -- loop body
            apply L1_hoare_seq
              (P := fun s => rb_count_above_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
              (R := fun s => rb_count_above_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
            · -- if cur->value <= threshold then count++ else skip
              apply L1_hoare_condition
              · intro s hpre
                obtain ⟨⟨h_inv, h_cond⟩, h_match⟩ := hpre
                constructor
                · intro hf; exact hf
                · intro r s' h_mem
                  have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                  match r with
                  | Except.ok () =>
                    subst hs
                    unfold rb_count_above_inv
                    rw [rb_count_above_inc_count_globals, rb_count_above_inc_count_locals_cur]
                    exact ⟨h_inv, h_cond⟩
                  | Except.error () =>
                    exact absurd hr (by intro h; cases h)
              · intro s hpre
                obtain ⟨⟨h_inv, h_cond⟩, h_nomatch⟩ := hpre
                constructor
                · intro hf; exact hf
                · intro r s' h_mem
                  have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                  match r with
                  | Except.ok () =>
                    subst hs
                    exact ⟨h_inv, h_cond⟩
                  | Except.error () =>
                    exact absurd hr (by intro h; cases h)
            · -- guard cur valid, then cur := cur->next
              intro s hpre
              obtain ⟨h_inv, h_cond⟩ := hpre
              unfold rb_count_above_inv at h_inv
              have h_ne : s.locals.cur ≠ Ptr.null := by
                simp only [decide_eq_true_eq] at h_cond
                exact h_cond
              have h_valid := h_inv.heapValid h_ne
              have h_tail := h_inv.tail h_ne
              have h_gm := L1_guard_modify_result
                (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cur)
                rb_count_above_set_cur_next s h_valid
              constructor
              · exact h_gm.2
              · intro r s' h_mem
                rw [h_gm.1] at h_mem
                have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                subst hr; subst hs
                unfold rb_count_above_inv
                rw [rb_count_above_set_cur_next_globals, rb_count_above_set_cur_next_locals_cur]
                exact h_tail
          · -- exit condition: while returns ok with invariant
            intro s h_inv _
            trivial
        · -- teardown: ret := count; throw
          intro s h_inv
          have h_mt := L1_modify_throw_result rb_count_above_set_ret_count s
          constructor
          · exact h_mt.2
          · intro r s' h_mem
            rw [h_mt.1] at h_mem
            have ⟨hr, hs⟩ := Prod.mk.inj h_mem
            subst hr; subst hs
            trivial
  · -- handler: skip
    intro _ _
    exact ⟨not_false, fun _ _ _ => trivial⟩

-- rb_swap_front_back: multi-step heap mutation (3 checks + 3 writes)
-- SORRY: The 3 conditions are eliminable (L1_hoare_condition + precondition contradictions).
-- The guard+modify chain after conditions needs ptrDisjoint(head, rb) and ptrDisjoint(tail, rb)
-- to show hVal of rb is unchanged after heapUpdate to head/tail nodes.
-- Without these, the guard predicates at intermediate states cannot be discharged.
-- Fix: add ptrDisjoint assumptions to rb_swap_front_back_spec.pre.
