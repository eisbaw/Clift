-- Proof for rb_reverse_validHoare (split from RBExtProofsSorry for memory)
-- rb_reverse: reverses a linked list in-place (prev/curr/next pointer reversal).
-- Pattern D (loop) with heap mutation (cur.next := prev per iteration).
-- Requires WellFormedList for pairwise disjointness through heap updates.
-- Template: RBExtProofRbFill.lean (loop with heap mutation, similar structure).
import Examples.RBExtSpecs
set_option maxHeartbeats 25600000
set_option maxRecDepth 4096
open RingBufferExt

/-! # Heap frame lemmas for WellFormedList through heapUpdate -/

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem AllDisjointFrom_heapUpdate_frame_rev
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
private theorem WellFormedList_heapUpdate_aux_rev
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
      (h_eq_q ▸ AllDisjointFrom_heapUpdate_frame_rev hsep_q (h_sep.adjtail hq) hv)

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem WellFormedList_heapUpdate_tail_rev
    {heap : HeapRawState} {p : Ptr C_rb_node} {v : C_rb_node}
    (h : WellFormedList heap p) (hp : p ≠ Ptr.null) (hv : heapPtrValid heap p)
    : WellFormedList (heapUpdate heap p v) (hVal heap p).next :=
  WellFormedList_heapUpdate_aux_rev (h.wf_tail hp) hv (h.headSep hp)

/-! # Loop invariant -/

/-- Loop invariant for the reversal loop.
    WellFormedList cur ensures that cur and all subsequent nodes are valid and pairwise disjoint.
    heapPtrValid rb ensures we can still access the rb_state struct after the loop. -/
private def rev_loop_inv (s : ProgramState) : Prop :=
  WellFormedList s.globals.rawHeap s.locals.cur ∧
  heapPtrValid s.globals.rawHeap s.locals.rb

/-! # Step functions (kernel depth avoidance) -/

-- ret__val := 1
private noncomputable def rev_set_ret1 (s : ProgramState) : ProgramState :=
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

-- ret__val := 0
private noncomputable def rev_set_ret0 (s : ProgramState) : ProgramState :=
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

-- old_head := (hVal heap rb).head
private noncomputable def rev_set_old_head (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt,
    (hVal s.globals.rawHeap s.locals.rb).head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

-- prev := Ptr.null
private noncomputable def rev_set_prev_null (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    Ptr.null, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

-- cur := (hVal heap rb).head
private noncomputable def rev_set_cur_head (s : ProgramState) : ProgramState :=
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

-- nxt := (hVal heap cur).next
private noncomputable def rev_set_nxt (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, (hVal s.globals.rawHeap s.locals.cur).next,
    s.locals.old_head, s.locals.old_val, s.locals.out_val, s.locals.pop_ok,
    s.locals.pop_result, s.locals.prev, s.locals.push_ok, s.locals.push_result,
    s.locals.rb, s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

-- prev := cur
private noncomputable def rev_set_prev_cur (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.cur, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

-- cur := nxt
private noncomputable def rev_set_cur_nxt (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.nxt, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

/-! # Funext lemmas -/

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rev_set_ret1_funext :
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := (1 : UInt32) } }) =
      rev_set_ret1 := by
  funext s; unfold rev_set_ret1; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rev_set_ret0_funext :
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := (0 : UInt32) } }) =
      rev_set_ret0 := by
  funext s; unfold rev_set_ret0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rev_set_old_head_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      old_head := (hVal s.globals.rawHeap s.locals.rb).head } }) = rev_set_old_head := by
  funext s; unfold rev_set_old_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rev_set_prev_null_funext :
    (fun s : ProgramState => { s with locals := { s.locals with prev := Ptr.null } }) =
      rev_set_prev_null := by
  funext s; unfold rev_set_prev_null; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rev_set_cur_head_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      cur := (hVal s.globals.rawHeap s.locals.rb).head } }) = rev_set_cur_head := by
  funext s; unfold rev_set_cur_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rev_set_nxt_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      nxt := (hVal s.globals.rawHeap s.locals.cur).next } }) = rev_set_nxt := by
  funext s; unfold rev_set_nxt; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rev_set_prev_cur_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      prev := s.locals.cur } }) = rev_set_prev_cur := by
  funext s; unfold rev_set_prev_cur; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rev_set_cur_nxt_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      cur := s.locals.nxt } }) = rev_set_cur_nxt := by
  funext s; unfold rev_set_cur_nxt; rfl

/-! # Projection lemmas -/

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rev_set_ret0_ret (s : ProgramState) :
    (rev_set_ret0 s).locals.ret__val = 0 := by unfold rev_set_ret0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rev_set_old_head_globals (s : ProgramState) :
    (rev_set_old_head s).globals = s.globals := by unfold rev_set_old_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rev_set_old_head_rb (s : ProgramState) :
    (rev_set_old_head s).locals.rb = s.locals.rb := by unfold rev_set_old_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rev_set_prev_null_globals (s : ProgramState) :
    (rev_set_prev_null s).globals = s.globals := by unfold rev_set_prev_null; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rev_set_prev_null_rb (s : ProgramState) :
    (rev_set_prev_null s).locals.rb = s.locals.rb := by unfold rev_set_prev_null; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rev_set_cur_head_globals (s : ProgramState) :
    (rev_set_cur_head s).globals = s.globals := by unfold rev_set_cur_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rev_set_cur_head_rb (s : ProgramState) :
    (rev_set_cur_head s).locals.rb = s.locals.rb := by unfold rev_set_cur_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rev_set_cur_head_cur (s : ProgramState) :
    (rev_set_cur_head s).locals.cur = (hVal s.globals.rawHeap s.locals.rb).head := by
  unfold rev_set_cur_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rev_set_nxt_globals (s : ProgramState) :
    (rev_set_nxt s).globals = s.globals := by unfold rev_set_nxt; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rev_set_nxt_cur (s : ProgramState) :
    (rev_set_nxt s).locals.cur = s.locals.cur := by unfold rev_set_nxt; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rev_set_nxt_nxt (s : ProgramState) :
    (rev_set_nxt s).locals.nxt = (hVal s.globals.rawHeap s.locals.cur).next := by
  unfold rev_set_nxt; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rev_set_nxt_prev (s : ProgramState) :
    (rev_set_nxt s).locals.prev = s.locals.prev := by unfold rev_set_nxt; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rev_set_nxt_rb (s : ProgramState) :
    (rev_set_nxt s).locals.rb = s.locals.rb := by unfold rev_set_nxt; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rev_set_prev_cur_globals (s : ProgramState) :
    (rev_set_prev_cur s).globals = s.globals := by unfold rev_set_prev_cur; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rev_set_prev_cur_cur (s : ProgramState) :
    (rev_set_prev_cur s).locals.cur = s.locals.cur := by unfold rev_set_prev_cur; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rev_set_prev_cur_nxt (s : ProgramState) :
    (rev_set_prev_cur s).locals.nxt = s.locals.nxt := by unfold rev_set_prev_cur; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rev_set_prev_cur_rb (s : ProgramState) :
    (rev_set_prev_cur s).locals.rb = s.locals.rb := by unfold rev_set_prev_cur; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rev_set_cur_nxt_globals (s : ProgramState) :
    (rev_set_cur_nxt s).globals = s.globals := by unfold rev_set_cur_nxt; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rev_set_cur_nxt_cur (s : ProgramState) :
    (rev_set_cur_nxt s).locals.cur = s.locals.nxt := by unfold rev_set_cur_nxt; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rev_set_cur_nxt_rb (s : ProgramState) :
    (rev_set_cur_nxt s).locals.rb = s.locals.rb := by unfold rev_set_cur_nxt; rfl

/-! # Main theorem -/

set_option maxRecDepth 8192 in
set_option maxHeartbeats 102400000 in
attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem rb_reverse_validHoare :
    rb_reverse_spec_ext.satisfiedBy RingBufferExt.l1_rb_reverse_body := by
  unfold FuncSpec.satisfiedBy rb_reverse_spec_ext
  unfold RingBufferExt.l1_rb_reverse_body
  simp only [rev_set_ret1_funext, rev_set_ret0_funext, rev_set_old_head_funext,
    rev_set_prev_null_funext, rev_set_cur_head_funext, rev_set_nxt_funext,
    rev_set_prev_cur_funext, rev_set_cur_nxt_funext]
  -- Structure: catch BODY skip
  -- BODY: seq (cond (count<2) (ret:=1; throw) skip)
  --         (seq (guard rb; old_head:=rb.head)
  --           (seq (prev:=null)
  --             (seq (guard rb; cur:=rb.head)
  --               (seq (while (...) LOOP_BODY)
  --                 (seq (guard rb; rb.head:=prev)
  --                   (seq (guard rb; rb.tail:=old_head)
  --                     (seq (ret:=0) throw)))))))
  -- Since the early-exit path (count<2) is excluded by precondition (count≥2),
  -- and the normal path always sets ret:=0 then throws, R = (ret=0) suffices.
  apply L1_hoare_catch (R := fun s => s.locals.ret__val = 0)
  · -- BODY
    apply L1_hoare_seq
      (P := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧
        WellFormedList s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head ∧
        (hVal s.globals.rawHeap s.locals.rb).count ≥ 2)
      (R := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧
        WellFormedList s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
    · -- cond (count < 2) (ret:=1; throw) skip
      apply L1_hoare_condition
      · -- TRUE: count < 2 → contradiction with count ≥ 2
        intro s hpre
        obtain ⟨⟨_, _, h_ge2⟩, h_cond⟩ := hpre
        simp only [decide_eq_true_eq] at h_cond
        exact absurd h_cond (not_lt.mpr h_ge2)
      · -- FALSE: skip
        intro s hpre
        obtain ⟨⟨h_rb, h_wf, _⟩, _⟩ := hpre
        constructor
        · intro hf; exact hf
        · intro r s' h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem
          subst hr; subst hs
          exact ⟨h_rb, h_wf⟩
    · -- seq (guard rb; old_head:=rb.head) REST
      apply L1_hoare_seq
        (R := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧
          WellFormedList s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
      · -- guard rb; old_head := rb.head
        intro s hpre
        obtain ⟨h_rb, h_wf⟩ := hpre
        have h_gm := L1_guard_modify_result
          (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
          rev_set_old_head s h_rb
        constructor
        · exact h_gm.2
        · intro r s' h_mem
          rw [h_gm.1] at h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem
          subst hr; subst hs
          rw [rev_set_old_head_globals, rev_set_old_head_rb]
          exact ⟨h_rb, h_wf⟩
      · -- seq (prev:=null) REST
        apply L1_hoare_seq
          (R := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧
            WellFormedList s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
        · -- prev := null
          intro s hpre
          obtain ⟨h_rb, h_wf⟩ := hpre
          constructor
          · intro hf; exact hf
          · intro r s' h_mem
            have ⟨hr, hs⟩ := Prod.mk.inj h_mem
            subst hr; subst hs
            rw [rev_set_prev_null_globals, rev_set_prev_null_rb]
            exact ⟨h_rb, h_wf⟩
        · -- seq (guard rb; cur:=rb.head) REST
          apply L1_hoare_seq (R := rev_loop_inv)
          · -- guard rb; cur := rb.head
            intro s hpre
            obtain ⟨h_rb, h_wf⟩ := hpre
            have h_gm := L1_guard_modify_result
              (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
              rev_set_cur_head s h_rb
            constructor
            · exact h_gm.2
            · intro r s' h_mem
              rw [h_gm.1] at h_mem
              have ⟨hr, hs⟩ := Prod.mk.inj h_mem
              subst hr; subst hs
              unfold rev_loop_inv
              rw [rev_set_cur_head_globals, rev_set_cur_head_cur, rev_set_cur_head_rb]
              exact ⟨h_wf, h_rb⟩
          · -- seq (while ...) (seq (guard rb; rb.head:=prev) ...)
            apply L1_hoare_seq (R := rev_loop_inv)
            · -- while (cur ≠ null) LOOP_BODY
              apply L1_hoare_while_from_body (I := rev_loop_inv)
              · -- Loop body: seq (guard cur; nxt:=cur.next)
                --   (seq (guard cur; cur.next:=prev) (seq (prev:=cur) (cur:=nxt)))
                -- This body never throws, so for L1_hoare_while_from_body:
                --   ok → I preserved; error → vacuous (never happens)
                -- Use L1_hoare_seq_ok for the 4-step chain since all are ok-producing.
                -- Actually the body IS a seq of seqs, so use L1_hoare_seq with ok-only reasoning.

                -- Step 1: guard cur; nxt := cur.next
                apply L1_hoare_seq
                  (P := fun s => rev_loop_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
                  (R := fun s => WellFormedList s.globals.rawHeap s.locals.cur ∧
                    heapPtrValid s.globals.rawHeap s.locals.rb ∧
                    s.locals.cur ≠ Ptr.null ∧
                    s.locals.nxt = (hVal s.globals.rawHeap s.locals.cur).next)
                · -- guard cur; nxt := cur.next
                  intro s hpre
                  obtain ⟨⟨h_wf, h_rb⟩, h_cond⟩ := hpre
                  have h_ne : s.locals.cur ≠ Ptr.null := by
                    simp only [decide_eq_true_eq] at h_cond; exact h_cond
                  have h_cur_v := h_wf.headValid h_ne
                  have h_gm := L1_guard_modify_result
                    (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cur)
                    rev_set_nxt s h_cur_v
                  constructor
                  · exact h_gm.2
                  · intro r s' h_mem
                    rw [h_gm.1] at h_mem
                    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                    subst hr; subst hs
                    rw [rev_set_nxt_globals, rev_set_nxt_cur, rev_set_nxt_rb]
                    exact ⟨h_wf, h_rb, h_ne, rev_set_nxt_nxt s⟩
                · -- Step 2: seq (guard cur; cur.next := prev) (seq (prev:=cur) (cur:=nxt))
                  apply L1_hoare_seq
                    (R := fun s => WellFormedList s.globals.rawHeap s.locals.nxt ∧
                      heapPtrValid s.globals.rawHeap s.locals.rb ∧
                      s.locals.cur ≠ Ptr.null)
                  · -- guard cur; heap[cur].next := prev (HEAP MUTATION)
                    intro s hpre
                    obtain ⟨h_wf, h_rb, h_ne, h_nxt_eq⟩ := hpre
                    have h_cur_v := h_wf.headValid h_ne
                    have h_gm := L1_guard_modify_result
                      (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cur)
                      (fun s => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.cur
                        ({ hVal s.globals.rawHeap s.locals.cur with next := s.locals.prev }) } })
                      s h_cur_v
                    constructor
                    · exact h_gm.2
                    · intro r s' h_mem
                      rw [h_gm.1] at h_mem
                      have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                      subst hr; subst hs
                      refine ⟨?_, ?_, ?_⟩
                      · -- WellFormedList (updated heap) nxt
                        -- nxt = (hVal old_heap cur).next (saved before the write)
                        -- WellFormedList_heapUpdate_tail_rev gives us:
                        --   WellFormedList (heapUpdate heap cur v) (hVal heap cur).next
                        -- which is exactly WellFormedList updated_heap nxt (since nxt = old_cur.next)
                        -- s'.locals.nxt = s.locals.nxt (locals unchanged by heap write)
                        -- s'.globals.rawHeap = heapUpdate s.globals.rawHeap s.locals.cur (...)
                        rw [h_nxt_eq]
                        exact WellFormedList_heapUpdate_tail_rev h_wf h_ne h_cur_v
                      · -- heapPtrValid (updated heap) rb
                        -- rb is Ptr C_rb_state, cur is Ptr C_rb_node → different types → disjoint
                        -- so heapUpdate at cur preserves heapPtrValid rb
                        exact heapUpdate_preserves_heapPtrValid _ _ _ _ h_rb
                      · exact h_ne
                  · -- seq (prev:=cur) (cur:=nxt)
                    apply L1_hoare_seq_ok
                      (R := fun s => WellFormedList s.globals.rawHeap s.locals.nxt ∧
                        heapPtrValid s.globals.rawHeap s.locals.rb)
                    · -- prev := cur
                      intro s hpre
                      obtain ⟨h_wf_nxt, h_rb, _⟩ := hpre
                      constructor
                      · intro hf; exact hf
                      · intro r s' h_mem
                        have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                        subst hr; subst hs
                        rw [rev_set_prev_cur_globals, rev_set_prev_cur_nxt, rev_set_prev_cur_rb]
                        exact ⟨h_wf_nxt, h_rb⟩
                    · -- cur := nxt
                      intro s hpre
                      obtain ⟨h_wf_nxt, h_rb⟩ := hpre
                      constructor
                      · intro hf; exact hf
                      · intro r s' h_mem
                        have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                        subst hr; subst hs
                        unfold rev_loop_inv
                        rw [rev_set_cur_nxt_globals, rev_set_cur_nxt_cur, rev_set_cur_nxt_rb]
                        exact ⟨h_wf_nxt, h_rb⟩
              · -- while exit: invariant holds
                intro s h_inv _; exact h_inv
            · -- post-loop: seq (guard rb; rb.head:=prev) (seq (guard rb; rb.tail:=old_head) (seq (ret:=0) throw))
              apply L1_hoare_seq
                (R := fun s => heapPtrValid s.globals.rawHeap s.locals.rb)
              · -- guard rb; rb.head := prev
                intro s hpre
                unfold rev_loop_inv at hpre
                obtain ⟨_, h_rb⟩ := hpre
                have h_gm := L1_guard_modify_result
                  (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
                  (fun s => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.rb
                    ({ hVal s.globals.rawHeap s.locals.rb with head := s.locals.prev }) } })
                  s h_rb
                constructor
                · exact h_gm.2
                · intro r s' h_mem
                  rw [h_gm.1] at h_mem
                  have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                  subst hr; subst hs
                  exact heapUpdate_preserves_heapPtrValid _ _ _ _ h_rb
              · -- seq (guard rb; rb.tail:=old_head) (seq (ret:=0) throw)
                apply L1_hoare_seq
                  (R := fun _ => True)
                · -- guard rb; rb.tail := old_head
                  intro s h_rb
                  have h_gm := L1_guard_modify_result
                    (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
                    (fun s => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.rb
                      ({ hVal s.globals.rawHeap s.locals.rb with tail := s.locals.old_head }) } })
                    s h_rb
                  constructor
                  · exact h_gm.2
                  · intro r s' h_mem
                    rw [h_gm.1] at h_mem
                    have ⟨_, hs⟩ := Prod.mk.inj h_mem; subst hs; trivial
                · -- seq (ret:=0) throw
                  intro s _
                  have h_mt := L1_modify_throw_result rev_set_ret0 s
                  constructor
                  · exact h_mt.2
                  · intro r s' h_mem
                    rw [h_mt.1] at h_mem
                    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                    subst hr; subst hs
                    rw [rev_set_ret0_ret]
  · -- handler: skip → postcondition
    intro s h_ret0
    constructor
    · intro hf; exact hf
    · intro r s' h_mem
      have ⟨hr, hs⟩ := Prod.mk.inj h_mem
      subst hr; subst hs
      intro _; exact h_ret0
