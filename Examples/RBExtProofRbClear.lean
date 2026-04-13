-- Proof for rb_clear_validHoare
-- rb_clear: traverses linked list zeroing each node's next pointer, then resets rb head/tail/count.
-- Pattern D (loop) + Pattern C (post-loop chain of 3 guard+modify on rb).
import Examples.RBExtSpecs
set_option maxHeartbeats 25600000
set_option maxRecDepth 4096
open RingBufferExt

/-! # Helper lemmas: WellFormedList preserved through heapUpdate -/

attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem AllDisjointFrom_heapUpdate_frame
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
private theorem WellFormedList_heapUpdate_aux
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
      (h_eq_q ▸ AllDisjointFrom_heapUpdate_frame hsep_q (h_sep.adjtail hq) hv)

attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem WellFormedList_heapUpdate_tail
    {heap : HeapRawState} {p : Ptr C_rb_node} {v : C_rb_node}
    (h : WellFormedList heap p) (hp : p ≠ Ptr.null) (hv : heapPtrValid heap p)
    : WellFormedList (heapUpdate heap p v) (hVal heap p).next :=
  WellFormedList_heapUpdate_aux (h.wf_tail hp) hv (h.headSep hp)

/-! # Loop invariant -/

private def rb_clear_inv (s : ProgramState) : Prop :=
  WellFormedList s.globals.rawHeap s.locals.cur ∧
  heapPtrValid s.globals.rawHeap s.locals.rb

/-- After saving nxt and doing the heap write. -/
private def rb_clear_after_write (s : ProgramState) : Prop :=
  WellFormedList s.globals.rawHeap s.locals.nxt ∧
  heapPtrValid s.globals.rawHeap s.locals.rb

/-! # Named step functions (anonymous constructors to avoid kernel depth issues) -/

-- removed := 0
private noncomputable def rb_clear_set_removed0 (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    (0 : UInt32), s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

-- cur := rb.head
private noncomputable def rb_clear_set_cur_head (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, (hVal s.globals.rawHeap s.locals.rb).head,
    s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

-- nxt := cur.next (guard cur valid; read cur.next)
private noncomputable def rb_clear_set_nxt (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, (hVal s.globals.rawHeap s.locals.cur).next,
    s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

-- heap[cur] := { cur_node with next := Ptr.null }
private noncomputable def rb_clear_heap_write (s : ProgramState) : ProgramState :=
  ⟨⟨heapUpdate s.globals.rawHeap s.locals.cur
      ({ hVal s.globals.rawHeap s.locals.cur with next := Ptr.null })⟩,
    s.locals⟩

-- cur := nxt
private noncomputable def rb_clear_set_cur_nxt (s : ProgramState) : ProgramState :=
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

-- removed++
private noncomputable def rb_clear_inc_removed (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    (s.locals.removed + 1), s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

-- heap[rb] := { rb_val with head := Ptr.null }
private noncomputable def rb_clear_set_head_null (s : ProgramState) : ProgramState :=
  ⟨⟨heapUpdate s.globals.rawHeap s.locals.rb
      ({ hVal s.globals.rawHeap s.locals.rb with head := Ptr.null })⟩,
    s.locals⟩

-- heap[rb] := { rb_val with tail := Ptr.null }
private noncomputable def rb_clear_set_tail_null (s : ProgramState) : ProgramState :=
  ⟨⟨heapUpdate s.globals.rawHeap s.locals.rb
      ({ hVal s.globals.rawHeap s.locals.rb with tail := Ptr.null })⟩,
    s.locals⟩

-- heap[rb] := { rb_val with count := 0 }
private noncomputable def rb_clear_set_count_0 (s : ProgramState) : ProgramState :=
  ⟨⟨heapUpdate s.globals.rawHeap s.locals.rb
      ({ hVal s.globals.rawHeap s.locals.rb with count := 0 })⟩,
    s.locals⟩

-- ret := removed
private noncomputable def rb_clear_set_ret (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.removed,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

/-! # Funext lemmas -/

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_set_removed0_funext :
    (fun s : ProgramState => { s with locals := { s.locals with removed := (0 : UInt32) } }) =
      rb_clear_set_removed0 := by
  funext s; unfold rb_clear_set_removed0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_set_cur_head_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      cur := (hVal s.globals.rawHeap s.locals.rb).head } }) = rb_clear_set_cur_head := by
  funext s; unfold rb_clear_set_cur_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_set_nxt_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      nxt := (hVal s.globals.rawHeap s.locals.cur).next } }) = rb_clear_set_nxt := by
  funext s; unfold rb_clear_set_nxt; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_heap_write_funext :
    (fun s : ProgramState => { s with globals := { s.globals with
      rawHeap := heapUpdate s.globals.rawHeap s.locals.cur
        ({ hVal s.globals.rawHeap s.locals.cur with next := Ptr.null }) } }) =
      rb_clear_heap_write := by
  funext s; unfold rb_clear_heap_write; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_set_cur_nxt_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      cur := s.locals.nxt } }) = rb_clear_set_cur_nxt := by
  funext s; unfold rb_clear_set_cur_nxt; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_inc_removed_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      removed := (s.locals.removed + 1) } }) = rb_clear_inc_removed := by
  funext s; unfold rb_clear_inc_removed; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_set_head_null_funext :
    (fun s : ProgramState => { s with globals := { s.globals with
      rawHeap := heapUpdate s.globals.rawHeap s.locals.rb
        ({ hVal s.globals.rawHeap s.locals.rb with head := Ptr.null }) } }) =
      rb_clear_set_head_null := by
  funext s; unfold rb_clear_set_head_null; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_set_tail_null_funext :
    (fun s : ProgramState => { s with globals := { s.globals with
      rawHeap := heapUpdate s.globals.rawHeap s.locals.rb
        ({ hVal s.globals.rawHeap s.locals.rb with tail := Ptr.null }) } }) =
      rb_clear_set_tail_null := by
  funext s; unfold rb_clear_set_tail_null; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_set_count_0_funext :
    (fun s : ProgramState => { s with globals := { s.globals with
      rawHeap := heapUpdate s.globals.rawHeap s.locals.rb
        ({ hVal s.globals.rawHeap s.locals.rb with count := 0 }) } }) =
      rb_clear_set_count_0 := by
  funext s; unfold rb_clear_set_count_0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_set_ret_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      ret__val := s.locals.removed } }) = rb_clear_set_ret := by
  funext s; unfold rb_clear_set_ret; rfl

/-! # Projection lemmas -/

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_set_removed0_globals (s : ProgramState) :
    (rb_clear_set_removed0 s).globals = s.globals := by unfold rb_clear_set_removed0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_set_removed0_locals_eq (s : ProgramState) :
    (rb_clear_set_removed0 s).locals =
      ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
        s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
        s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
        s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
        s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
        s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
        s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
        (0 : UInt32), s.locals.replaced, s.locals.result, s.locals.ret__val,
        s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
        s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
        s.locals.transferred, s.locals.val⟩ := by
  show (⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    (0 : UInt32), s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩ : ProgramState).locals = _
  rfl

@[simp] private theorem rb_clear_set_removed0_locals_rb (s : ProgramState) :
    (rb_clear_set_removed0 s).locals.rb = s.locals.rb := by rw [rb_clear_set_removed0_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_set_cur_head_globals (s : ProgramState) :
    (rb_clear_set_cur_head s).globals = s.globals := by unfold rb_clear_set_cur_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_set_cur_head_locals_eq (s : ProgramState) :
    (rb_clear_set_cur_head s).locals =
      ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
        s.locals.cb, s.locals.count, (hVal s.globals.rawHeap s.locals.rb).head,
        s.locals.current_count, s.locals.delta,
        s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
        s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
        s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
        s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
        s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
        s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
        s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
        s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
        s.locals.transferred, s.locals.val⟩ := by
  show (⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, (hVal s.globals.rawHeap s.locals.rb).head,
    s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩ : ProgramState).locals = _
  rfl

@[simp] private theorem rb_clear_set_cur_head_locals_cur (s : ProgramState) :
    (rb_clear_set_cur_head s).locals.cur = (hVal s.globals.rawHeap s.locals.rb).head := by
  rw [rb_clear_set_cur_head_locals_eq]

@[simp] private theorem rb_clear_set_cur_head_locals_rb (s : ProgramState) :
    (rb_clear_set_cur_head s).locals.rb = s.locals.rb := by
  rw [rb_clear_set_cur_head_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_set_nxt_globals (s : ProgramState) :
    (rb_clear_set_nxt s).globals = s.globals := by unfold rb_clear_set_nxt; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_set_nxt_locals_eq (s : ProgramState) :
    (rb_clear_set_nxt s).locals =
      ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
        s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
        s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
        s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
        s.locals.n, s.locals.new_val, s.locals.node, (hVal s.globals.rawHeap s.locals.cur).next,
        s.locals.old_head,
        s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
        s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
        s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
        s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
        s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
        s.locals.transferred, s.locals.val⟩ := by
  show (⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, (hVal s.globals.rawHeap s.locals.cur).next,
    s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩ : ProgramState).locals = _
  rfl

@[simp] private theorem rb_clear_set_nxt_locals_cur (s : ProgramState) :
    (rb_clear_set_nxt s).locals.cur = s.locals.cur := by rw [rb_clear_set_nxt_locals_eq]

@[simp] private theorem rb_clear_set_nxt_locals_nxt (s : ProgramState) :
    (rb_clear_set_nxt s).locals.nxt = (hVal s.globals.rawHeap s.locals.cur).next := by
  rw [rb_clear_set_nxt_locals_eq]

@[simp] private theorem rb_clear_set_nxt_locals_rb (s : ProgramState) :
    (rb_clear_set_nxt s).locals.rb = s.locals.rb := by rw [rb_clear_set_nxt_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_heap_write_globals_rawHeap (s : ProgramState) :
    (rb_clear_heap_write s).globals.rawHeap =
      heapUpdate s.globals.rawHeap s.locals.cur
        ({ hVal s.globals.rawHeap s.locals.cur with next := Ptr.null }) := by
  unfold rb_clear_heap_write; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_heap_write_locals (s : ProgramState) :
    (rb_clear_heap_write s).locals = s.locals := by unfold rb_clear_heap_write; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_heap_write_locals_cur (s : ProgramState) :
    (rb_clear_heap_write s).locals.cur = s.locals.cur := by unfold rb_clear_heap_write; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_heap_write_locals_nxt (s : ProgramState) :
    (rb_clear_heap_write s).locals.nxt = s.locals.nxt := by unfold rb_clear_heap_write; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_heap_write_locals_rb (s : ProgramState) :
    (rb_clear_heap_write s).locals.rb = s.locals.rb := by unfold rb_clear_heap_write; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_set_cur_nxt_globals (s : ProgramState) :
    (rb_clear_set_cur_nxt s).globals = s.globals := by unfold rb_clear_set_cur_nxt; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_set_cur_nxt_locals_eq (s : ProgramState) :
    (rb_clear_set_cur_nxt s).locals =
      ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
        s.locals.cb, s.locals.count, s.locals.nxt, s.locals.current_count, s.locals.delta,
        s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
        s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
        s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
        s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
        s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
        s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
        s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
        s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
        s.locals.transferred, s.locals.val⟩ := by
  show (⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.nxt, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩ : ProgramState).locals = _
  rfl

@[simp] private theorem rb_clear_set_cur_nxt_locals_cur (s : ProgramState) :
    (rb_clear_set_cur_nxt s).locals.cur = s.locals.nxt := by rw [rb_clear_set_cur_nxt_locals_eq]

@[simp] private theorem rb_clear_set_cur_nxt_locals_rb (s : ProgramState) :
    (rb_clear_set_cur_nxt s).locals.rb = s.locals.rb := by rw [rb_clear_set_cur_nxt_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_inc_removed_globals (s : ProgramState) :
    (rb_clear_inc_removed s).globals = s.globals := by unfold rb_clear_inc_removed; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_inc_removed_locals_eq (s : ProgramState) :
    (rb_clear_inc_removed s).locals =
      ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
        s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
        s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
        s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
        s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
        s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
        s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
        (s.locals.removed + 1), s.locals.replaced, s.locals.result, s.locals.ret__val,
        s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
        s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
        s.locals.transferred, s.locals.val⟩ := by
  show (⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    (s.locals.removed + 1), s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩ : ProgramState).locals = _
  rfl

@[simp] private theorem rb_clear_inc_removed_locals_cur (s : ProgramState) :
    (rb_clear_inc_removed s).locals.cur = s.locals.cur := by rw [rb_clear_inc_removed_locals_eq]

@[simp] private theorem rb_clear_inc_removed_locals_nxt (s : ProgramState) :
    (rb_clear_inc_removed s).locals.nxt = s.locals.nxt := by rw [rb_clear_inc_removed_locals_eq]

@[simp] private theorem rb_clear_inc_removed_locals_rb (s : ProgramState) :
    (rb_clear_inc_removed s).locals.rb = s.locals.rb := by rw [rb_clear_inc_removed_locals_eq]

-- Post-loop step projection lemmas

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_set_head_null_locals (s : ProgramState) :
    (rb_clear_set_head_null s).locals = s.locals := by unfold rb_clear_set_head_null; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_set_head_null_locals_rb (s : ProgramState) :
    (rb_clear_set_head_null s).locals.rb = s.locals.rb := by unfold rb_clear_set_head_null; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_set_head_null_globals_rawHeap (s : ProgramState) :
    (rb_clear_set_head_null s).globals.rawHeap =
      heapUpdate s.globals.rawHeap s.locals.rb
        ({ hVal s.globals.rawHeap s.locals.rb with head := Ptr.null }) := by
  unfold rb_clear_set_head_null; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_set_tail_null_locals (s : ProgramState) :
    (rb_clear_set_tail_null s).locals = s.locals := by unfold rb_clear_set_tail_null; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_set_tail_null_locals_rb (s : ProgramState) :
    (rb_clear_set_tail_null s).locals.rb = s.locals.rb := by unfold rb_clear_set_tail_null; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_set_tail_null_globals_rawHeap (s : ProgramState) :
    (rb_clear_set_tail_null s).globals.rawHeap =
      heapUpdate s.globals.rawHeap s.locals.rb
        ({ hVal s.globals.rawHeap s.locals.rb with tail := Ptr.null }) := by
  unfold rb_clear_set_tail_null; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_set_count_0_locals (s : ProgramState) :
    (rb_clear_set_count_0 s).locals = s.locals := by unfold rb_clear_set_count_0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_set_count_0_locals_rb (s : ProgramState) :
    (rb_clear_set_count_0 s).locals.rb = s.locals.rb := by unfold rb_clear_set_count_0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_set_count_0_globals_rawHeap (s : ProgramState) :
    (rb_clear_set_count_0 s).globals.rawHeap =
      heapUpdate s.globals.rawHeap s.locals.rb
        ({ hVal s.globals.rawHeap s.locals.rb with count := 0 }) := by
  unfold rb_clear_set_count_0; rfl

/-! # Helper: loop body validHoare -/

set_option maxRecDepth 8192 in
set_option maxHeartbeats 51200000 in
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_loop_body_hoare :
    validHoare
      (fun s => rb_clear_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
      (L1.seq
        (L1.seq (L1.guard (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cur))
          (L1.modify rb_clear_set_nxt))
        (L1.seq
          (L1.seq (L1.guard (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cur))
            (L1.modify rb_clear_heap_write))
          (L1.seq (L1.modify rb_clear_set_cur_nxt) (L1.modify rb_clear_inc_removed))))
      (fun r s => match r with | .ok () => rb_clear_inv s | .error () => False) := by
  apply L1_hoare_seq
    (P := fun s => rb_clear_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
    (R := fun s =>
      WellFormedList s.globals.rawHeap s.locals.cur ∧
      heapPtrValid s.globals.rawHeap s.locals.rb ∧
      s.locals.nxt = (hVal s.globals.rawHeap s.locals.cur).next ∧
      heapPtrValid s.globals.rawHeap s.locals.cur ∧
      s.locals.cur ≠ Ptr.null)
  · -- guard cur valid; nxt := cur.next
    intro s hpre
    obtain ⟨h_inv, h_cond⟩ := hpre
    unfold rb_clear_inv at h_inv
    obtain ⟨h_wf, h_rb_valid⟩ := h_inv
    have h_ne : s.locals.cur ≠ Ptr.null := by
      simp only [decide_eq_true_eq] at h_cond; exact h_cond
    have h_cur_valid := h_wf.headValid h_ne
    have h_gm := L1_guard_modify_result (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cur) rb_clear_set_nxt s h_cur_valid
    constructor
    · exact h_gm.2
    · intro r s' h_mem
      rw [h_gm.1] at h_mem
      have ⟨hr, hs⟩ := Prod.mk.inj h_mem
      subst hr; subst hs
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [rb_clear_set_nxt_globals, rb_clear_set_nxt_locals_cur]; exact h_wf
      · rw [rb_clear_set_nxt_globals]; exact h_rb_valid
      · rw [rb_clear_set_nxt_globals, rb_clear_set_nxt_locals_cur]
        exact rb_clear_set_nxt_locals_nxt s
      · rw [rb_clear_set_nxt_globals, rb_clear_set_nxt_locals_cur]; exact h_cur_valid
      · rw [rb_clear_set_nxt_locals_cur]; exact h_ne
  · -- seq (guard cur; heap write) (seq (cur:=nxt) (removed++))
    apply L1_hoare_seq
      (P := fun s =>
        WellFormedList s.globals.rawHeap s.locals.cur ∧
        heapPtrValid s.globals.rawHeap s.locals.rb ∧
        s.locals.nxt = (hVal s.globals.rawHeap s.locals.cur).next ∧
        heapPtrValid s.globals.rawHeap s.locals.cur ∧
        s.locals.cur ≠ Ptr.null)
      (R := rb_clear_after_write)
    · -- guard cur valid; heap[cur] := { cur with next := null }
      intro s hpre
      obtain ⟨h_wf, h_rb_valid, h_nxt_eq, h_cur_valid, h_ne⟩ := hpre
      have h_gm := L1_guard_modify_result (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cur) rb_clear_heap_write s h_cur_valid
      constructor
      · exact h_gm.2
      · intro r s' h_mem
        rw [h_gm.1] at h_mem
        have ⟨hr, hs⟩ := Prod.mk.inj h_mem
        subst hr; subst hs
        unfold rb_clear_after_write
        refine ⟨?_, ?_⟩
        · rw [rb_clear_heap_write_globals_rawHeap, rb_clear_heap_write_locals_nxt, h_nxt_eq]
          exact WellFormedList_heapUpdate_tail h_wf h_ne h_cur_valid
        · rw [rb_clear_heap_write_globals_rawHeap, rb_clear_heap_write_locals_rb]
          exact heapUpdate_preserves_heapPtrValid _ _ _ _ h_rb_valid
    · -- seq (cur := nxt) (removed++)
      apply L1_hoare_seq (P := rb_clear_after_write) (R := rb_clear_inv)
      · -- cur := nxt
        intro s hpre
        obtain ⟨h_wf_nxt, h_rb_valid⟩ := hpre
        constructor
        · intro hf; exact hf
        · intro r s' h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem
          match r with
          | Except.ok () =>
            subst hs; unfold rb_clear_inv
            exact ⟨by rw [rb_clear_set_cur_nxt_globals, rb_clear_set_cur_nxt_locals_cur]; exact h_wf_nxt,
                   by rw [rb_clear_set_cur_nxt_globals]; exact h_rb_valid⟩
          | Except.error () => exact absurd hr (by intro h; cases h)
      · -- removed++
        intro s h_inv
        unfold rb_clear_inv at h_inv
        obtain ⟨h_wf, h_rb_valid⟩ := h_inv
        constructor
        · intro hf; exact hf
        · intro r s' h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem
          match r with
          | Except.ok () =>
            subst hs; unfold rb_clear_inv
            exact ⟨by rw [rb_clear_inc_removed_globals, rb_clear_inc_removed_locals_cur]; exact h_wf,
                   by rw [rb_clear_inc_removed_globals]; exact h_rb_valid⟩
          | Except.error () => exact absurd hr (by intro h; cases h)

/-! # Helper: post-loop chain validHoare -/

set_option maxRecDepth 8192 in
set_option maxHeartbeats 51200000 in
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_clear_postloop_hoare :
    validHoare rb_clear_inv
      (L1.seq
        (L1.seq (L1.guard (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb))
          (L1.modify rb_clear_set_head_null))
        (L1.seq
          (L1.seq (L1.guard (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb))
            (L1.modify rb_clear_set_tail_null))
          (L1.seq
            (L1.seq (L1.guard (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb))
              (L1.modify rb_clear_set_count_0))
            (L1.seq (L1.modify rb_clear_set_ret) L1.throw))))
      (fun r s => match r with
        | .ok () => True
        | .error () =>
          (hVal s.globals.rawHeap s.locals.rb).head = Ptr.null ∧
          (hVal s.globals.rawHeap s.locals.rb).tail = Ptr.null ∧
          (hVal s.globals.rawHeap s.locals.rb).count = 0) := by
  apply L1_hoare_seq
    (R := fun s =>
      heapPtrValid s.globals.rawHeap s.locals.rb ∧
      (hVal s.globals.rawHeap s.locals.rb).head = Ptr.null)
  · -- guard rb; heap[rb].head := null
    intro s hpre
    unfold rb_clear_inv at hpre
    obtain ⟨_, h_rb_valid⟩ := hpre
    have h_gm := L1_guard_modify_result (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb) rb_clear_set_head_null s h_rb_valid
    constructor
    · exact h_gm.2
    · intro r s' h_mem
      rw [h_gm.1] at h_mem
      have ⟨hr, hs⟩ := Prod.mk.inj h_mem
      subst hr; subst hs
      refine ⟨?_, ?_⟩
      · rw [rb_clear_set_head_null_globals_rawHeap, rb_clear_set_head_null_locals_rb]
        exact heapUpdate_preserves_heapPtrValid _ _ _ _ h_rb_valid
      · rw [rb_clear_set_head_null_globals_rawHeap, rb_clear_set_head_null_locals_rb]
        rw [hVal_heapUpdate_same _ _ _ (heapPtrValid_bound h_rb_valid)]
  · apply L1_hoare_seq
      (R := fun s =>
        heapPtrValid s.globals.rawHeap s.locals.rb ∧
        (hVal s.globals.rawHeap s.locals.rb).head = Ptr.null ∧
        (hVal s.globals.rawHeap s.locals.rb).tail = Ptr.null)
    · -- guard rb; heap[rb].tail := null
      intro s hpre
      obtain ⟨h_rb_valid, h_head_null⟩ := hpre
      have h_gm := L1_guard_modify_result (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb) rb_clear_set_tail_null s h_rb_valid
      constructor
      · exact h_gm.2
      · intro r s' h_mem
        rw [h_gm.1] at h_mem
        have ⟨hr, hs⟩ := Prod.mk.inj h_mem
        subst hr; subst hs
        refine ⟨?_, ?_, ?_⟩
        · rw [rb_clear_set_tail_null_globals_rawHeap, rb_clear_set_tail_null_locals_rb]
          exact heapUpdate_preserves_heapPtrValid _ _ _ _ h_rb_valid
        · rw [rb_clear_set_tail_null_globals_rawHeap, rb_clear_set_tail_null_locals_rb]
          rw [hVal_heapUpdate_same _ _ _ (heapPtrValid_bound h_rb_valid)]
          exact h_head_null
        · rw [rb_clear_set_tail_null_globals_rawHeap, rb_clear_set_tail_null_locals_rb]
          rw [hVal_heapUpdate_same _ _ _ (heapPtrValid_bound h_rb_valid)]
    · apply L1_hoare_seq
        (R := fun s =>
          (hVal s.globals.rawHeap s.locals.rb).head = Ptr.null ∧
          (hVal s.globals.rawHeap s.locals.rb).tail = Ptr.null ∧
          (hVal s.globals.rawHeap s.locals.rb).count = 0)
      · -- guard rb; heap[rb].count := 0
        intro s hpre
        obtain ⟨h_rb_valid, h_head_null, h_tail_null⟩ := hpre
        have h_gm := L1_guard_modify_result (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb) rb_clear_set_count_0 s h_rb_valid
        constructor
        · exact h_gm.2
        · intro r s' h_mem
          rw [h_gm.1] at h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem
          subst hr; subst hs
          refine ⟨?_, ?_, ?_⟩
          · rw [rb_clear_set_count_0_globals_rawHeap, rb_clear_set_count_0_locals_rb]
            rw [hVal_heapUpdate_same _ _ _ (heapPtrValid_bound h_rb_valid)]
            exact h_head_null
          · rw [rb_clear_set_count_0_globals_rawHeap, rb_clear_set_count_0_locals_rb]
            rw [hVal_heapUpdate_same _ _ _ (heapPtrValid_bound h_rb_valid)]
            exact h_tail_null
          · rw [rb_clear_set_count_0_globals_rawHeap, rb_clear_set_count_0_locals_rb]
            rw [hVal_heapUpdate_same _ _ _ (heapPtrValid_bound h_rb_valid)]
      · -- ret := removed; throw
        intro s hpre
        obtain ⟨h_head, h_tail, h_count⟩ := hpre
        have h_mt := L1_modify_throw_result rb_clear_set_ret s
        constructor
        · exact h_mt.2
        · intro r s' h_mem
          rw [h_mt.1] at h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem
          subst hr; subst hs
          exact ⟨h_head, h_tail, h_count⟩

/-! # Main theorem -/

set_option maxRecDepth 16384 in
set_option maxHeartbeats 102400000 in
attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem rb_clear_validHoare :
    rb_clear_spec_ext.satisfiedBy RingBufferExt.l1_rb_clear_body := by
  unfold FuncSpec.satisfiedBy rb_clear_spec_ext
  unfold RingBufferExt.l1_rb_clear_body
  simp only [rb_clear_set_removed0_funext, rb_clear_set_cur_head_funext,
    rb_clear_set_nxt_funext, rb_clear_heap_write_funext,
    rb_clear_set_cur_nxt_funext, rb_clear_inc_removed_funext,
    rb_clear_set_head_null_funext, rb_clear_set_tail_null_funext,
    rb_clear_set_count_0_funext, rb_clear_set_ret_funext]
  apply L1_hoare_catch (R := fun s =>
    (hVal s.globals.rawHeap s.locals.rb).head = Ptr.null ∧
    (hVal s.globals.rawHeap s.locals.rb).tail = Ptr.null ∧
    (hVal s.globals.rawHeap s.locals.rb).count = 0)
  · -- Body
    apply L1_hoare_seq (R := fun s =>
      heapPtrValid s.globals.rawHeap s.locals.rb ∧
      WellFormedList s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
    · -- removed := 0
      intro s hpre
      obtain ⟨h_rb, h_wf⟩ := hpre
      constructor
      · intro hf; exact hf
      · intro r s' h_mem
        have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
        rw [rb_clear_set_removed0_globals]
        exact ⟨h_rb, h_wf⟩
    · -- seq (guard rb; cur:=head) (seq (while) (post-loop))
      apply L1_hoare_seq (R := rb_clear_inv)
      · -- guard rb valid, then cur := rb.head
        intro s hpre
        obtain ⟨h_rb, h_wf⟩ := hpre
        have h_gm := L1_guard_modify_result (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb) rb_clear_set_cur_head s h_rb
        constructor
        · exact h_gm.2
        · intro r s' h_mem
          rw [h_gm.1] at h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem
          subst hr; subst hs
          unfold rb_clear_inv
          exact ⟨by rw [rb_clear_set_cur_head_globals, rb_clear_set_cur_head_locals_cur]; exact h_wf,
                 by rw [rb_clear_set_cur_head_globals]; exact h_rb⟩
      · -- seq (while) (post-loop)
        apply L1_hoare_seq (R := rb_clear_inv)
        · -- while loop
          apply L1_hoare_while_from_body
          · exact rb_clear_loop_body_hoare
          · intro s h_inv _; exact h_inv
        · -- post-loop chain
          exact rb_clear_postloop_hoare
  · -- handler: skip → postcondition
    intro s hpost
    constructor
    · intro hf; exact hf
    · intro r s' h_mem
      have ⟨hr, hs⟩ := Prod.mk.inj h_mem
      subst hr; subst hs
      intro _
      exact hpost
