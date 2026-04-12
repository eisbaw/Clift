-- Proof for rb_fill_validHoare (split from RBExtProofsSorry for memory)
-- rb_fill: traverses linked list, sets every node's value to fill_value (s.locals.val).
-- Pattern D (loop) with heap mutation per iteration.
-- Key: WellFormedList provides pairwise disjointness needed for heap frame reasoning.
-- Template: RBExtProofRbIncrementAll.lean (identical structure, different heap write).
import Examples.RBExtSpecs
set_option maxHeartbeats 25600000
set_option maxRecDepth 4096
open RingBufferExt

/-! # Heap frame lemmas for WellFormedList through heapUpdate -/

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem AllDisjointFrom_heapUpdate_frame_fill
    {heap : HeapRawState} {q r : Ptr C_rb_node} {v : C_rb_node} {p : Ptr C_rb_node}
    (hadj_q : AllDisjointFrom heap q p) (hadj_r : AllDisjointFrom heap r p)
    (hr : heapPtrValid heap r)
    : AllDisjointFrom (heapUpdate heap r v) q p := by
  induction hadj_q with
  | null => exact AllDisjointFrom.null
  | cons p' hp' hv' hdisj_qp' _ ih =>
    exact AllDisjointFrom.cons p' hp'
      (heapUpdate_preserves_heapPtrValid heap r v p' hv') hdisj_qp'
      (hVal_heapUpdate_disjoint heap r p' v (heapPtrValid_bound hr)
        (heapPtrValid_bound hv') (hadj_r.headDisjoint hp') ▸ ih (hadj_r.adjtail hp'))

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem WellFormedList_heapUpdate_aux_fill
    {heap : HeapRawState} {p : Ptr C_rb_node} {v : C_rb_node} {nxt : Ptr C_rb_node}
    (hwf : WellFormedList heap nxt) (hv : heapPtrValid heap p)
    (h_sep : AllDisjointFrom heap p nxt)
    : WellFormedList (heapUpdate heap p v) nxt := by
  induction hwf with
  | null => exact WellFormedList.null
  | @cons q hq hv_q _ hsep_q ih =>
    have h_eq_q := hVal_heapUpdate_disjoint heap p q v (heapPtrValid_bound hv)
      (heapPtrValid_bound hv_q) (h_sep.headDisjoint hq)
    exact WellFormedList.cons q hq (heapUpdate_preserves_heapPtrValid heap p v q hv_q)
      (h_eq_q ▸ ih (h_sep.adjtail hq))
      (h_eq_q ▸ AllDisjointFrom_heapUpdate_frame_fill hsep_q (h_sep.adjtail hq) hv)

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem WellFormedList_heapUpdate_tail_fill
    {heap : HeapRawState} {p : Ptr C_rb_node} {v : C_rb_node}
    (h : WellFormedList heap p) (hp : p ≠ Ptr.null) (hv : heapPtrValid heap p)
    : WellFormedList (heapUpdate heap p v) (hVal heap p).next :=
  WellFormedList_heapUpdate_aux_fill (h.wf_tail hp) hv (h.headSep hp)

/-! # Loop invariant -/

private def rb_fill_inv (s : ProgramState) : Prop :=
  WellFormedList s.globals.rawHeap s.locals.cur

/-- After heap write: tail is well-formed, cur is valid, and cur ≠ null. -/
private def rb_fill_after_write (s : ProgramState) : Prop :=
  WellFormedList s.globals.rawHeap (hVal s.globals.rawHeap s.locals.cur).next ∧
  heapPtrValid s.globals.rawHeap s.locals.cur ∧
  s.locals.cur ≠ Ptr.null

/-! # Named functions for each basic operation -/

-- filled := 0
private noncomputable def rb_fill_set_filled0 (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, (0 : UInt32), s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

-- cur := rb.head
private noncomputable def rb_fill_set_cur (s : ProgramState) : ProgramState :=
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

-- heap[cur].value := val (modifies globals.rawHeap)
private noncomputable def rb_fill_heap_write (s : ProgramState) : ProgramState :=
  ⟨⟨heapUpdate s.globals.rawHeap s.locals.cur
      ({ hVal s.globals.rawHeap s.locals.cur with
        value := s.locals.val })⟩,
    s.locals⟩

-- filled++
private noncomputable def rb_fill_inc_filled (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, (s.locals.filled + 1), s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

-- cur := cur.next (reads from current heap state)
private noncomputable def rb_fill_set_cur_next (s : ProgramState) : ProgramState :=
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

-- ret := filled
private noncomputable def rb_fill_set_ret (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.filled,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

/-! # Funext lemmas -/

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_fill_set_filled0_funext :
    (fun s : ProgramState => { s with locals := { s.locals with filled := (0 : UInt32) } }) =
      rb_fill_set_filled0 := by
  funext s; unfold rb_fill_set_filled0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_fill_set_cur_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      cur := (hVal s.globals.rawHeap s.locals.rb).head } }) = rb_fill_set_cur := by
  funext s; unfold rb_fill_set_cur; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_fill_heap_write_funext :
    (fun s : ProgramState => { s with globals := { s.globals with
      rawHeap := heapUpdate s.globals.rawHeap s.locals.cur
        ({ hVal s.globals.rawHeap s.locals.cur with
          value := s.locals.val }) } }) =
      rb_fill_heap_write := by
  funext s; unfold rb_fill_heap_write; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_fill_inc_filled_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      filled := (s.locals.filled + 1) } }) = rb_fill_inc_filled := by
  funext s; unfold rb_fill_inc_filled; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_fill_set_cur_next_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      cur := (hVal s.globals.rawHeap s.locals.cur).next } }) = rb_fill_set_cur_next := by
  funext s; unfold rb_fill_set_cur_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_fill_set_ret_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      ret__val := s.locals.filled } }) = rb_fill_set_ret := by
  funext s; unfold rb_fill_set_ret; rfl

/-! # Projection lemmas -/

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_fill_set_filled0_globals (s : ProgramState) :
    (rb_fill_set_filled0 s).globals = s.globals := by unfold rb_fill_set_filled0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_fill_set_cur_globals (s : ProgramState) :
    (rb_fill_set_cur s).globals = s.globals := by unfold rb_fill_set_cur; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_fill_set_cur_locals_cur (s : ProgramState) :
    (rb_fill_set_cur s).locals.cur = (hVal s.globals.rawHeap s.locals.rb).head := by
  unfold rb_fill_set_cur; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_fill_heap_write_globals_rawHeap (s : ProgramState) :
    (rb_fill_heap_write s).globals.rawHeap =
      heapUpdate s.globals.rawHeap s.locals.cur
        ({ hVal s.globals.rawHeap s.locals.cur with
          value := s.locals.val }) := by
  unfold rb_fill_heap_write; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_fill_heap_write_locals (s : ProgramState) :
    (rb_fill_heap_write s).locals = s.locals := by unfold rb_fill_heap_write; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_fill_heap_write_locals_cur (s : ProgramState) :
    (rb_fill_heap_write s).locals.cur = s.locals.cur := by unfold rb_fill_heap_write; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_fill_inc_filled_globals (s : ProgramState) :
    (rb_fill_inc_filled s).globals = s.globals := by unfold rb_fill_inc_filled; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_fill_inc_filled_locals_cur (s : ProgramState) :
    (rb_fill_inc_filled s).locals.cur = s.locals.cur := by unfold rb_fill_inc_filled; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_fill_set_cur_next_globals (s : ProgramState) :
    (rb_fill_set_cur_next s).globals = s.globals := by unfold rb_fill_set_cur_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_fill_set_cur_next_locals_cur (s : ProgramState) :
    (rb_fill_set_cur_next s).locals.cur = (hVal s.globals.rawHeap s.locals.cur).next := by
  unfold rb_fill_set_cur_next; rfl

/-! # Main theorem -/

set_option maxRecDepth 8192 in
set_option maxHeartbeats 51200000 in
attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem rb_fill_validHoare :
    rb_fill_spec.satisfiedBy RingBufferExt.l1_rb_fill_body := by
  unfold FuncSpec.satisfiedBy rb_fill_spec
  unfold RingBufferExt.l1_rb_fill_body
  simp only [rb_fill_set_filled0_funext, rb_fill_set_cur_funext,
    rb_fill_heap_write_funext, rb_fill_inc_filled_funext,
    rb_fill_set_cur_next_funext, rb_fill_set_ret_funext]
  -- Structure: catch (seq (filled:=0) (seq (guard rb; cur:=head) (seq (while ...) (seq (ret:=filled) throw)))) skip
  -- Postcondition is trivially true (each field = itself), so we only need non-failure.
  apply L1_hoare_catch (R := fun _ => True)
  · -- Body
    apply L1_hoare_seq (R := fun s =>
      heapPtrValid s.globals.rawHeap s.locals.rb ∧
      WellFormedList s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
    · -- filled := 0
      intro s hpre
      obtain ⟨h_rb, h_wf⟩ := hpre
      constructor
      · intro hf; exact hf
      · intro r s' h_mem
        have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
        rw [rb_fill_set_filled0_globals]
        exact ⟨h_rb, h_wf⟩
    · -- seq (guard rb; cur:=head) (seq (while ...) (seq (ret:=filled) throw))
      apply L1_hoare_seq (R := rb_fill_inv)
      · -- guard rb valid, then cur := rb.head
        intro s hpre
        obtain ⟨h_rb, h_wf⟩ := hpre
        have h_gm := L1_guard_modify_result
          (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
          rb_fill_set_cur s h_rb
        constructor
        · exact h_gm.2
        · intro r s' h_mem
          rw [h_gm.1] at h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem
          subst hr; subst hs
          unfold rb_fill_inv
          rw [rb_fill_set_cur_globals, rb_fill_set_cur_locals_cur]
          exact h_wf
      · -- seq (while ...) (seq (ret:=filled) throw)
        apply L1_hoare_seq (R := rb_fill_inv)
        · -- while loop
          apply L1_hoare_while_from_body
          · -- loop body: seq (guard cur; heap_write) (seq (filled++) (guard cur; cur:=next))
            apply L1_hoare_seq
              (P := fun s => rb_fill_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
              (R := rb_fill_after_write)
            · -- guard cur; heap_write (heap[cur].value := val)
              intro s hpre
              obtain ⟨h_inv, h_cond⟩ := hpre
              unfold rb_fill_inv at h_inv
              have h_ne : s.locals.cur ≠ Ptr.null := by
                simp only [decide_eq_true_eq] at h_cond; exact h_cond
              have h_valid := h_inv.headValid h_ne
              have h_gm := L1_guard_modify_result
                (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cur)
                rb_fill_heap_write s h_valid
              constructor
              · exact h_gm.2
              · intro r s' h_mem
                rw [h_gm.1] at h_mem
                have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                subst hr; subst hs
                unfold rb_fill_after_write
                refine ⟨?_, ?_, ?_⟩
                · -- WellFormedList of tail in updated heap
                  rw [rb_fill_heap_write_globals_rawHeap, rb_fill_heap_write_locals_cur]
                  have h_bound := heapPtrValid_bound h_valid
                  rw [hVal_heapUpdate_same _ _ _ h_bound]
                  exact WellFormedList_heapUpdate_tail_fill h_inv h_ne h_valid
                · -- heapPtrValid cur in updated heap
                  rw [rb_fill_heap_write_globals_rawHeap, rb_fill_heap_write_locals_cur]
                  exact heapUpdate_preserves_heapPtrValid _ _ _ _ h_valid
                · -- cur ≠ null
                  rw [rb_fill_heap_write_locals_cur]
                  exact h_ne
            · -- seq (filled++) (guard cur; cur := cur.next)
              apply L1_hoare_seq
                (P := rb_fill_after_write)
                (R := rb_fill_after_write)
              · -- filled++
                intro s hpre
                obtain ⟨h_wf_tail, h_valid, h_ne⟩ := hpre
                constructor
                · intro hf; exact hf
                · intro r s' h_mem
                  have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                  match r with
                  | Except.ok () =>
                    subst hs
                    unfold rb_fill_after_write
                    refine ⟨?_, ?_, ?_⟩
                    · rw [rb_fill_inc_filled_globals, rb_fill_inc_filled_locals_cur]; exact h_wf_tail
                    · rw [rb_fill_inc_filled_globals, rb_fill_inc_filled_locals_cur]; exact h_valid
                    · rw [show (rb_fill_inc_filled s).locals.cur = s.locals.cur from rb_fill_inc_filled_locals_cur s]
                      exact h_ne
                  | Except.error () =>
                    exact absurd hr (by intro h; cases h)
              · -- guard cur valid; cur := cur.next
                intro s hpre
                obtain ⟨h_wf_tail, h_valid, h_ne⟩ := hpre
                have h_gm := L1_guard_modify_result
                  (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cur)
                  rb_fill_set_cur_next s h_valid
                constructor
                · exact h_gm.2
                · intro r s' h_mem
                  rw [h_gm.1] at h_mem
                  have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                  subst hr; subst hs
                  unfold rb_fill_inv
                  rw [rb_fill_set_cur_next_globals, rb_fill_set_cur_next_locals_cur]
                  exact h_wf_tail
          · -- exit: while returns ok with invariant preserved
            intro s h_inv _
            exact h_inv
        · -- teardown: seq (ret:=filled) throw
          intro s h_inv
          have h_mt := L1_modify_throw_result rb_fill_set_ret s
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
      exact ⟨trivial, trivial, trivial, trivial⟩
