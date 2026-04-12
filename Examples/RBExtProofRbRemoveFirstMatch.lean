-- Proof for rb_remove_first_match_validHoare (split from RBExtProofsSorry for memory)
-- rb_remove_first_match: traverses list, removes first node matching a value.
-- Pattern D (loop) with conditional node removal + pointer relinking.
-- Postcondition is weak (ret__val ∈ {0,1}), main challenge is non-failure through guards.
import Examples.RBExtSpecs
set_option maxHeartbeats 25600000
set_option maxRecDepth 4096
open RingBufferExt

/-! # Step functions for local-variable modifications (kernel depth avoidance) -/

-- ret__val := 1
private noncomputable def rfm_set_ret1 (s : ProgramState) : ProgramState :=
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
private noncomputable def rfm_set_ret0 (s : ProgramState) : ProgramState :=
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

-- cur := (hVal heap rb).head
private noncomputable def rfm_set_cur_head (s : ProgramState) : ProgramState :=
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

-- prev := (hVal heap rb).head
private noncomputable def rfm_set_prev_head (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    (hVal s.globals.rawHeap s.locals.rb).head, s.locals.push_ok, s.locals.push_result,
    s.locals.rb, s.locals.removed, s.locals.replaced, s.locals.result,
    s.locals.ret__val, s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

-- cur := (hVal heap (hVal heap rb).head).next
private noncomputable def rfm_set_cur_head_next (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count,
    (hVal s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head).next,
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

-- prev := cur
private noncomputable def rfm_set_prev_cur (s : ProgramState) : ProgramState :=
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

-- cur := (hVal heap cur).next
private noncomputable def rfm_set_cur_next (s : ProgramState) : ProgramState :=
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

/-! # Funext lemmas -/

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_ret1_funext :
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := (1 : UInt32) } }) =
      rfm_set_ret1 := by
  funext s; unfold rfm_set_ret1; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_ret0_funext :
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := (0 : UInt32) } }) =
      rfm_set_ret0 := by
  funext s; unfold rfm_set_ret0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_cur_head_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      cur := (hVal s.globals.rawHeap s.locals.rb).head } }) = rfm_set_cur_head := by
  funext s; unfold rfm_set_cur_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_prev_head_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      prev := (hVal s.globals.rawHeap s.locals.rb).head } }) = rfm_set_prev_head := by
  funext s; unfold rfm_set_prev_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_cur_head_next_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      cur := (hVal s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head).next } }) =
      rfm_set_cur_head_next := by
  funext s; unfold rfm_set_cur_head_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_prev_cur_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      prev := s.locals.cur } }) = rfm_set_prev_cur := by
  funext s; unfold rfm_set_prev_cur; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_cur_next_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      cur := (hVal s.globals.rawHeap s.locals.cur).next } }) = rfm_set_cur_next := by
  funext s; unfold rfm_set_cur_next; rfl

/-! # Projection lemmas -/

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_ret1_globals (s : ProgramState) :
    (rfm_set_ret1 s).globals = s.globals := by unfold rfm_set_ret1; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_ret1_ret (s : ProgramState) :
    (rfm_set_ret1 s).locals.ret__val = 1 := by unfold rfm_set_ret1; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_ret0_globals (s : ProgramState) :
    (rfm_set_ret0 s).globals = s.globals := by unfold rfm_set_ret0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_ret0_ret (s : ProgramState) :
    (rfm_set_ret0 s).locals.ret__val = 0 := by unfold rfm_set_ret0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_cur_head_globals (s : ProgramState) :
    (rfm_set_cur_head s).globals = s.globals := by unfold rfm_set_cur_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_cur_head_cur (s : ProgramState) :
    (rfm_set_cur_head s).locals.cur = (hVal s.globals.rawHeap s.locals.rb).head := by
  unfold rfm_set_cur_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_cur_head_rb (s : ProgramState) :
    (rfm_set_cur_head s).locals.rb = s.locals.rb := by unfold rfm_set_cur_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_prev_head_globals (s : ProgramState) :
    (rfm_set_prev_head s).globals = s.globals := by unfold rfm_set_prev_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_prev_head_prev (s : ProgramState) :
    (rfm_set_prev_head s).locals.prev = (hVal s.globals.rawHeap s.locals.rb).head := by
  unfold rfm_set_prev_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_prev_head_rb (s : ProgramState) :
    (rfm_set_prev_head s).locals.rb = s.locals.rb := by unfold rfm_set_prev_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_prev_head_cur (s : ProgramState) :
    (rfm_set_prev_head s).locals.cur = s.locals.cur := by unfold rfm_set_prev_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_cur_head_next_globals (s : ProgramState) :
    (rfm_set_cur_head_next s).globals = s.globals := by unfold rfm_set_cur_head_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_cur_head_next_cur (s : ProgramState) :
    (rfm_set_cur_head_next s).locals.cur =
      (hVal s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head).next := by
  unfold rfm_set_cur_head_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_cur_head_next_rb (s : ProgramState) :
    (rfm_set_cur_head_next s).locals.rb = s.locals.rb := by unfold rfm_set_cur_head_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_cur_head_next_prev (s : ProgramState) :
    (rfm_set_cur_head_next s).locals.prev = s.locals.prev := by
  unfold rfm_set_cur_head_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_prev_cur_globals (s : ProgramState) :
    (rfm_set_prev_cur s).globals = s.globals := by unfold rfm_set_prev_cur; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_prev_cur_prev (s : ProgramState) :
    (rfm_set_prev_cur s).locals.prev = s.locals.cur := by unfold rfm_set_prev_cur; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_prev_cur_cur (s : ProgramState) :
    (rfm_set_prev_cur s).locals.cur = s.locals.cur := by unfold rfm_set_prev_cur; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_prev_cur_rb (s : ProgramState) :
    (rfm_set_prev_cur s).locals.rb = s.locals.rb := by unfold rfm_set_prev_cur; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_cur_next_globals (s : ProgramState) :
    (rfm_set_cur_next s).globals = s.globals := by unfold rfm_set_cur_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_cur_next_cur (s : ProgramState) :
    (rfm_set_cur_next s).locals.cur = (hVal s.globals.rawHeap s.locals.cur).next := by
  unfold rfm_set_cur_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_cur_next_prev (s : ProgramState) :
    (rfm_set_cur_next s).locals.prev = s.locals.prev := by unfold rfm_set_cur_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_cur_next_rb (s : ProgramState) :
    (rfm_set_cur_next s).locals.rb = s.locals.rb := by unfold rfm_set_cur_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_prev_head_val (s : ProgramState) :
    (rfm_set_prev_head s).locals.val = s.locals.val := by unfold rfm_set_prev_head; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rfm_set_cur_head_next_val (s : ProgramState) :
    (rfm_set_cur_head_next s).locals.val = s.locals.val := by unfold rfm_set_cur_head_next; rfl

/-! # Loop invariant -/

/-- Loop invariant for the search loop.
    The loop doesn't mutate the heap on the non-matching (ok) path,
    so LinkedListValid for cur is sufficient. On the matching (throw) path,
    we prove guards individually. -/
private def rfm_loop_inv (s : ProgramState) : Prop :=
  heapPtrValid s.globals.rawHeap s.locals.rb ∧
  LinkedListValid s.globals.rawHeap s.locals.cur ∧
  heapPtrValid s.globals.rawHeap s.locals.prev ∧
  -- prev.next = cur in current heap (for relinking on match)
  (hVal s.globals.rawHeap s.locals.prev).next = s.locals.cur

/-! # Main theorem -/

set_option maxRecDepth 8192 in
set_option maxHeartbeats 102400000 in
attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem rb_remove_first_match_validHoare :
    rb_remove_first_match_spec.satisfiedBy RingBufferExt.l1_rb_remove_first_match_body := by
  unfold FuncSpec.satisfiedBy rb_remove_first_match_spec
  unfold RingBufferExt.l1_rb_remove_first_match_body
  simp only [rfm_set_ret1_funext, rfm_set_ret0_funext, rfm_set_cur_head_funext,
    rfm_set_prev_head_funext, rfm_set_cur_head_next_funext, rfm_set_prev_cur_funext,
    rfm_set_cur_next_funext]
  -- Overall Q for catch body: fun r s => match r with | ok => ret ∈ {0,1} | error => ret ∈ {0,1}
  -- Since postcondition is: r = ok → ret ∈ {0,1}, and catch converts all errors to ok,
  -- we use R = ret ∈ {0,1} for the error-to-handler path.
  apply L1_hoare_catch (R := fun s => s.locals.ret__val = 0 ∨ s.locals.ret__val = 1)
  · -- BODY: seq COND_EMPTY (seq COND_HEAD REST)
    -- The overall postcondition for body:
    --   ok → ret ∈ {0,1}  (body never produces ok, but formally needed)
    --   error → ret ∈ {0,1}
    apply L1_hoare_seq
      (P := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧
        WellFormedList s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
      (R := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧
        WellFormedList s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head ∧
        (hVal s.globals.rawHeap s.locals.rb).head ≠ Ptr.null)
    · -- COND_EMPTY: cond (rb.head = null) (ret:=1; throw) skip
      apply L1_hoare_condition
      · -- TRUE: head = null → ret:=1, throw
        intro s hpre
        obtain ⟨⟨h_rb, h_wf⟩, h_eq⟩ := hpre
        have h_mt := L1_modify_throw_result rfm_set_ret1 s
        constructor
        · exact h_mt.2
        · intro r s' h_mem
          rw [h_mt.1] at h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem
          subst hr; subst hs
          -- r = error, need: ret ∈ {0,1}
          rw [rfm_set_ret1_ret]; exact Or.inr rfl
      · -- FALSE: head ≠ null → skip
        intro s hpre
        obtain ⟨⟨h_rb, h_wf⟩, h_false⟩ := hpre
        constructor
        · intro hf; exact hf
        · intro r s' h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem
          subst hr; subst hs
          -- r = ok, need: R s
          have h_ne : (hVal s.globals.rawHeap s.locals.rb).head ≠ Ptr.null := by
            simp only [decide_eq_true_eq] at h_false; exact h_false
          exact ⟨h_rb, h_wf, h_ne⟩
    · -- seq COND_HEAD REST
      -- COND_HEAD: cond (head.value = val) REMOVE_HEAD skip
      -- REST: prev:=head; cur:=head.next; while(...); ret:=1; throw
      apply L1_hoare_seq
        (R := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧
          WellFormedList s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head ∧
          (hVal s.globals.rawHeap s.locals.rb).head ≠ Ptr.null)
      · -- COND_HEAD
        apply L1_hoare_condition
        · -- TRUE: head.value = val → REMOVE_HEAD (ends in throw with ret=0)
          -- Structure: seq (guard rb; cur:=head) (seq (guard rb; guard cur; rb.head:=cur.next)
          --   (seq (cond (rb.head=null) (guard rb; rb.tail:=null) skip)
          --     (seq (guard cur; cur.next:=null) (seq (guard rb; guard rb; rb.count--) (seq (ret:=0) throw)))))
          -- We need to prove all guards succeed and the final state has ret=0.
          -- Since this path ends in throw, the postcondition for L1_hoare_seq's m₁ needs:
          --   error → ret ∈ {0,1}   (the outer Q error case)
          -- We chain through seq by tracking validity.
          apply L1_hoare_seq
            (R := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧
              heapPtrValid s.globals.rawHeap s.locals.cur ∧
              s.locals.cur = (hVal s.globals.rawHeap s.locals.rb).head ∧
              WellFormedList s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head ∧
              (hVal s.globals.rawHeap s.locals.rb).head ≠ Ptr.null)
          · -- guard rb; cur := rb.head
            intro s hpre
            obtain ⟨⟨h_rb, h_wf, h_ne⟩, _⟩ := hpre
            have h_gm := L1_guard_modify_result
              (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
              rfm_set_cur_head s h_rb
            constructor
            · exact h_gm.2
            · intro r s' h_mem
              rw [h_gm.1] at h_mem
              have ⟨hr, hs⟩ := Prod.mk.inj h_mem
              subst hr; subst hs
              rw [rfm_set_cur_head_globals, rfm_set_cur_head_rb]
              exact ⟨h_rb, by rw [rfm_set_cur_head_cur]; exact h_wf.headValid h_ne,
                     rfm_set_cur_head_cur s, h_wf, h_ne⟩
          · -- rest of REMOVE_HEAD
            apply L1_hoare_seq
              (R := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧
                heapPtrValid s.globals.rawHeap s.locals.cur)
            · -- guard rb; guard cur; rb.head := cur.next
              intro s hpre
              obtain ⟨h_rb, h_cur_v, _, _, _⟩ := hpre
              have h_ggm := L1_guard_guard_modify_result
                (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
                (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cur)
                (fun s => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.rb
                  ({ hVal s.globals.rawHeap s.locals.rb with head := (hVal s.globals.rawHeap s.locals.cur).next }) } })
                s h_rb h_cur_v
              constructor
              · exact h_ggm.2
              · intro r s' h_mem
                rw [h_ggm.1] at h_mem
                have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                subst hr; subst hs
                exact ⟨heapUpdate_preserves_heapPtrValid _ _ _ _ h_rb,
                       heapUpdate_preserves_heapPtrValid _ _ _ _ h_cur_v⟩
            · -- seq (cond tail_check) (seq (cur.next:=null) (seq (count--) (seq (ret:=0) throw)))
              apply L1_hoare_seq
                (R := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧
                  heapPtrValid s.globals.rawHeap s.locals.cur)
              · -- cond (rb.head = null): true → rb.tail := null; false → skip
                apply L1_hoare_condition
                · -- TRUE: rb.head = null
                  intro s hpre
                  obtain ⟨⟨h_rb, h_cur_v⟩, _⟩ := hpre
                  have h_gm := L1_guard_modify_result
                    (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
                    (fun s => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.rb
                      ({ hVal s.globals.rawHeap s.locals.rb with tail := Ptr.null }) } })
                    s h_rb
                  constructor
                  · exact h_gm.2
                  · intro r s' h_mem
                    rw [h_gm.1] at h_mem
                    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                    subst hr; subst hs
                    exact ⟨heapUpdate_preserves_heapPtrValid _ _ _ _ h_rb,
                           heapUpdate_preserves_heapPtrValid _ _ _ _ h_cur_v⟩
                · -- FALSE: skip
                  intro s hpre
                  obtain ⟨⟨h_rb, h_cur_v⟩, _⟩ := hpre
                  constructor
                  · intro hf; exact hf
                  · intro r s' h_mem
                    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                    subst hr; subst hs
                    exact ⟨h_rb, h_cur_v⟩
              · -- seq (guard cur; cur.next:=null) (seq (guard rb; guard rb; count--) (seq (ret:=0) throw))
                apply L1_hoare_seq
                  (R := fun s => heapPtrValid s.globals.rawHeap s.locals.rb)
                · -- guard cur; cur.next := null
                  intro s hpre
                  obtain ⟨h_rb, h_cur_v⟩ := hpre
                  have h_gm := L1_guard_modify_result
                    (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cur)
                    (fun s => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.cur
                      ({ hVal s.globals.rawHeap s.locals.cur with next := Ptr.null }) } })
                    s h_cur_v
                  constructor
                  · exact h_gm.2
                  · intro r s' h_mem
                    rw [h_gm.1] at h_mem
                    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                    subst hr; subst hs
                    exact heapUpdate_preserves_heapPtrValid _ _ _ _ h_rb
                · -- seq (guard rb; guard rb; count--) (seq (ret:=0) throw)
                  apply L1_hoare_seq
                    (R := fun _ => True)
                  · -- guard rb; guard rb; rb.count := rb.count - 1
                    intro s h_rb
                    have h_ggm := L1_guard_guard_modify_result
                      (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
                      (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
                      (fun s => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.rb
                        ({ hVal s.globals.rawHeap s.locals.rb with count := (hVal s.globals.rawHeap s.locals.rb).count - 1 }) } })
                      s h_rb h_rb
                    constructor
                    · exact h_ggm.2
                    · intro r s' h_mem
                      rw [h_ggm.1] at h_mem
                      have ⟨_, hs⟩ := Prod.mk.inj h_mem; subst hs; trivial
                  · -- seq (ret:=0) throw
                    intro s _
                    have h_mt := L1_modify_throw_result rfm_set_ret0 s
                    constructor
                    · exact h_mt.2
                    · intro r s' h_mem
                      rw [h_mt.1] at h_mem
                      have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                      subst hr; subst hs
                      rw [rfm_set_ret0_ret]; exact Or.inl rfl
        · -- FALSE: head.value ≠ val → skip
          intro s hpre
          obtain ⟨⟨h_rb, h_wf, h_ne⟩, _⟩ := hpre
          constructor
          · intro hf; exact hf
          · intro r s' h_mem
            have ⟨hr, hs⟩ := Prod.mk.inj h_mem
            subst hr; subst hs
            exact ⟨h_rb, h_wf, h_ne⟩
      · -- REST: seq (guard rb; prev:=head) (seq (guard head; cur:=head.next) (seq (while ...) (seq (ret:=1) throw)))
        apply L1_hoare_seq
          (R := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧
            WellFormedList s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head ∧
            (hVal s.globals.rawHeap s.locals.rb).head ≠ Ptr.null ∧
            s.locals.prev = (hVal s.globals.rawHeap s.locals.rb).head)
        · -- guard rb; prev := rb.head
          intro s hpre
          obtain ⟨h_rb, h_wf, h_ne⟩ := hpre
          have h_gm := L1_guard_modify_result
            (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
            rfm_set_prev_head s h_rb
          constructor
          · exact h_gm.2
          · intro r s' h_mem
            rw [h_gm.1] at h_mem
            have ⟨hr, hs⟩ := Prod.mk.inj h_mem
            subst hr; subst hs
            rw [rfm_set_prev_head_globals, rfm_set_prev_head_rb]
            exact ⟨h_rb, h_wf, h_ne, rfm_set_prev_head_prev s⟩
        · -- seq (guard head; cur:=head.next) (seq (while ...) (seq (ret:=1) throw))
          apply L1_hoare_seq
            (R := rfm_loop_inv)
          · -- guard (heapPtrValid head); cur := head.next
            intro s hpre
            obtain ⟨h_rb, h_wf, h_ne, h_prev_eq⟩ := hpre
            have h_head_v := h_wf.headValid h_ne
            have h_gm := L1_guard_modify_result
              (fun s : ProgramState => heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
              rfm_set_cur_head_next s h_head_v
            constructor
            · exact h_gm.2
            · intro r s' h_mem
              rw [h_gm.1] at h_mem
              have ⟨hr, hs⟩ := Prod.mk.inj h_mem
              subst hr; subst hs
              unfold rfm_loop_inv
              rw [rfm_set_cur_head_next_globals, rfm_set_cur_head_next_rb]
              refine ⟨h_rb, ?_, ?_, ?_⟩
              · -- LinkedListValid cur (= head.next)
                rw [rfm_set_cur_head_next_cur]
                exact (h_wf.toLinkedListValid.tail h_ne)
              · -- heapPtrValid prev (= head)
                rw [rfm_set_cur_head_next_prev, h_prev_eq]
                exact h_head_v
              · -- prev.next = cur
                rw [rfm_set_cur_head_next_prev, rfm_set_cur_head_next_cur, h_prev_eq]
          · -- seq (while ...) (seq (ret:=1) throw)
            apply L1_hoare_seq
              (R := rfm_loop_inv)
            · -- while (cur ≠ null) LOOP_BODY
              apply L1_hoare_while_from_body (I := rfm_loop_inv)
              · -- Loop body: seq (cond (cur.value=val) REMOVE skip) (seq (prev:=cur) (guard cur; cur:=cur.next))
                -- On ok (no match): advance prev/cur, maintain invariant
                -- On error (match): unlink node, ret:=0, throw
                apply L1_hoare_seq
                  (P := fun s => rfm_loop_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
                  (R := fun s => rfm_loop_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
                · -- cond (cur.value = val) REMOVE skip
                  apply L1_hoare_condition
                  · -- TRUE: cur.value = val → REMOVE (unlink cur, ret:=0, throw)
                    -- This produces error, so need: outer Q error = ret ∈ {0,1}
                    -- Structure: seq (guard prev; guard cur; prev.next := cur.next)
                    --   (seq (cond (cur=rb.tail) (guard rb; rb.tail:=prev) skip)
                    --     (seq (guard cur; cur.next:=null)
                    --       (seq (guard rb; guard rb; rb.count--)
                    --         (seq (ret:=0) throw))))
                    apply L1_hoare_seq
                      (R := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧
                        heapPtrValid s.globals.rawHeap s.locals.cur)
                    · -- guard prev; guard cur; prev.next := cur.next
                      intro s hpre
                      obtain ⟨⟨⟨h_rb, _, h_prev_v, _⟩, h_cond⟩, _⟩ := hpre
                      have h_ne : s.locals.cur ≠ Ptr.null := by
                        simp only [decide_eq_true_eq] at h_cond; exact h_cond
                      have h_cur_v : heapPtrValid s.globals.rawHeap s.locals.cur := by
                        obtain ⟨_, h_llv, _, _⟩ := hpre.1
                        exact h_llv.headValid h_ne
                      have h_ggm := L1_guard_guard_modify_result
                        (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.prev)
                        (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cur)
                        (fun s => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.prev
                          ({ hVal s.globals.rawHeap s.locals.prev with next := (hVal s.globals.rawHeap s.locals.cur).next }) } })
                        s h_prev_v h_cur_v
                      constructor
                      · exact h_ggm.2
                      · intro r s' h_mem
                        rw [h_ggm.1] at h_mem
                        have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                        subst hr; subst hs
                        exact ⟨heapUpdate_preserves_heapPtrValid _ _ _ _ h_rb,
                               heapUpdate_preserves_heapPtrValid _ _ _ _ h_cur_v⟩
                    · -- seq (cond tail_check) (seq (cur.next:=null) (seq (count--) (seq (ret:=0) throw)))
                      apply L1_hoare_seq
                        (R := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧
                          heapPtrValid s.globals.rawHeap s.locals.cur)
                      · -- cond (cur = rb.tail): true → rb.tail := prev; false → skip
                        apply L1_hoare_condition
                        · -- TRUE
                          intro s hpre
                          obtain ⟨⟨h_rb, h_cur_v⟩, _⟩ := hpre
                          have h_gm := L1_guard_modify_result
                            (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
                            (fun s => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.rb
                              ({ hVal s.globals.rawHeap s.locals.rb with tail := s.locals.prev }) } })
                            s h_rb
                          constructor
                          · exact h_gm.2
                          · intro r s' h_mem
                            rw [h_gm.1] at h_mem
                            have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                            subst hr; subst hs
                            exact ⟨heapUpdate_preserves_heapPtrValid _ _ _ _ h_rb,
                                   heapUpdate_preserves_heapPtrValid _ _ _ _ h_cur_v⟩
                        · -- FALSE: skip
                          intro s hpre
                          obtain ⟨⟨h_rb, h_cur_v⟩, _⟩ := hpre
                          constructor
                          · intro hf; exact hf
                          · intro r s' h_mem
                            have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                            subst hr; subst hs
                            exact ⟨h_rb, h_cur_v⟩
                      · -- seq (guard cur; cur.next:=null) (seq (guard rb; guard rb; count--) (seq (ret:=0) throw))
                        apply L1_hoare_seq
                          (R := fun s => heapPtrValid s.globals.rawHeap s.locals.rb)
                        · -- guard cur; cur.next := null
                          intro s hpre
                          obtain ⟨h_rb, h_cur_v⟩ := hpre
                          have h_gm := L1_guard_modify_result
                            (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cur)
                            (fun s => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.cur
                              ({ hVal s.globals.rawHeap s.locals.cur with next := Ptr.null }) } })
                            s h_cur_v
                          constructor
                          · exact h_gm.2
                          · intro r s' h_mem
                            rw [h_gm.1] at h_mem
                            have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                            subst hr; subst hs
                            exact heapUpdate_preserves_heapPtrValid _ _ _ _ h_rb
                        · -- seq (guard rb; guard rb; count--) (seq (ret:=0) throw)
                          apply L1_hoare_seq
                            (R := fun _ => True)
                          · -- guard rb; guard rb; rb.count--
                            intro s h_rb
                            have h_ggm := L1_guard_guard_modify_result
                              (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
                              (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
                              (fun s => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.rb
                                ({ hVal s.globals.rawHeap s.locals.rb with count := (hVal s.globals.rawHeap s.locals.rb).count - 1 }) } })
                              s h_rb h_rb
                            constructor
                            · exact h_ggm.2
                            · intro r s' h_mem
                              rw [h_ggm.1] at h_mem
                              have ⟨_, hs⟩ := Prod.mk.inj h_mem; subst hs; trivial
                          · -- seq (ret:=0) throw
                            intro s _
                            have h_mt := L1_modify_throw_result rfm_set_ret0 s
                            constructor
                            · exact h_mt.2
                            · intro r s' h_mem
                              rw [h_mt.1] at h_mem
                              have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                              subst hr; subst hs
                              rw [rfm_set_ret0_ret]; exact Or.inl rfl
                  · -- FALSE: cur.value ≠ val → skip
                    intro s hpre
                    obtain ⟨⟨h_inv, h_cond⟩, _⟩ := hpre
                    constructor
                    · intro hf; exact hf
                    · intro r s' h_mem
                      have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                      subst hr; subst hs
                      exact ⟨h_inv, h_cond⟩
                · -- seq (prev:=cur) (guard cur; cur:=cur.next) — advance
                  apply L1_hoare_seq_ok
                    (R := fun s => rfm_loop_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true ∧
                      s.locals.prev = s.locals.cur)
                  · -- prev := cur
                    intro s hpre
                    obtain ⟨⟨h_rb, h_llv, h_prev_v, h_prev_next⟩, h_cond⟩ := hpre
                    have h_ne : s.locals.cur ≠ Ptr.null := by
                      simp only [decide_eq_true_eq] at h_cond; exact h_cond
                    have h_cur_v := h_llv.headValid h_ne
                    constructor
                    · intro hf; exact hf
                    · intro r s' h_mem
                      have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                      subst hr; subst hs
                      constructor
                      · exact rfl
                      · unfold rfm_loop_inv
                        rw [rfm_set_prev_cur_globals, rfm_set_prev_cur_rb, rfm_set_prev_cur_cur]
                        refine ⟨⟨h_rb, h_llv, ?_, ?_⟩, h_cond, rfm_set_prev_cur_prev s⟩
                        · -- heapPtrValid prev' (= cur)
                          rw [rfm_set_prev_cur_prev]; exact h_cur_v
                        · -- prev'.next = cur
                          rw [rfm_set_prev_cur_prev]
                  · -- guard cur; cur := cur.next
                    intro s hpre
                    obtain ⟨⟨h_rb, h_llv, h_prev_v, h_prev_next⟩, h_cond, h_prev_eq⟩ := hpre
                    have h_ne : s.locals.cur ≠ Ptr.null := by
                      simp only [decide_eq_true_eq] at h_cond; exact h_cond
                    have h_cur_v := h_llv.headValid h_ne
                    have h_gm := L1_guard_modify_result
                      (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cur)
                      rfm_set_cur_next s h_cur_v
                    constructor
                    · exact h_gm.2
                    · intro r s' h_mem
                      rw [h_gm.1] at h_mem
                      have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                      subst hr; subst hs
                      unfold rfm_loop_inv
                      rw [rfm_set_cur_next_globals, rfm_set_cur_next_rb]
                      refine ⟨h_rb, ?_, ?_, ?_⟩
                      · -- LinkedListValid cur' (= cur.next)
                        rw [rfm_set_cur_next_cur]; exact h_llv.tail h_ne
                      · -- heapPtrValid prev
                        rw [rfm_set_cur_next_prev]; exact h_prev_v
                      · -- prev.next = cur'
                        rw [rfm_set_cur_next_prev, rfm_set_cur_next_cur, h_prev_eq]
              · -- while exit: invariant holds, cur = null
                intro s h_inv _; exact h_inv
            · -- seq (ret:=1) throw — not found
              intro s h_inv
              have h_mt := L1_modify_throw_result rfm_set_ret1 s
              constructor
              · exact h_mt.2
              · intro r s' h_mem
                rw [h_mt.1] at h_mem
                have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                subst hr; subst hs
                rw [rfm_set_ret1_ret]; exact Or.inr rfl
  · -- handler: skip → postcondition
    intro s h_retval
    constructor
    · intro hf; exact hf
    · intro r s' h_mem
      have ⟨hr, hs⟩ := Prod.mk.inj h_mem
      subst hr; subst hs
      intro _; exact h_retval
