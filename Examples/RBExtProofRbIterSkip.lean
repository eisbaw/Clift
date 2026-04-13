-- Proof for rb_iter_skip_validHoare (split from RBExtProofsSorry for memory)
import Examples.RBExtSpecs
set_option maxHeartbeats 51200000
set_option maxRecDepth 8192
open RingBufferExt

-- Type tag disjointness: C_rb_iter (203) vs C_rb_node (200)
private theorem C_rb_iter_node_typeTag_ne :
    @CType.typeTag C_rb_iter _ ≠ @CType.typeTag C_rb_node _ := by decide

private theorem iter_node_disjoint {h : HeapRawState} {p : Ptr C_rb_iter} {q : Ptr C_rb_node}
    (hp : heapPtrValid h p) (hq : heapPtrValid h q) :
    ptrDisjoint p q :=
  heapPtrValid_different_type_disjoint hp hq C_rb_iter_node_typeTag_ne

-- LinkedListValid is preserved through heapUpdate at a C_rb_iter pointer
private theorem LinkedListValid_heapUpdate_iter
    {h : HeapRawState} {iter : Ptr C_rb_iter} {v : C_rb_iter} {p : Ptr C_rb_node}
    (hiter : heapPtrValid h iter)
    (hll : LinkedListValid h p) :
    LinkedListValid (heapUpdate h iter v) p := by
  induction hll with
  | null => exact LinkedListValid.null
  | cons q hq_ne hq_valid hq_tail ih =>
    apply LinkedListValid.cons q hq_ne
    · exact heapUpdate_preserves_heapPtrValid h iter v q hq_valid
    · have hbiter := heapPtrValid_bound hiter
      have hbq := heapPtrValid_bound hq_valid
      have hdisj := iter_node_disjoint hiter hq_valid
      rw [hVal_heapUpdate_disjoint h iter q v hbiter hbq hdisj]
      exact ih

-- hVal after heapUpdate at the same pointer
private theorem hVal_update_self {h : HeapRawState} {p : Ptr C_rb_iter} {v : C_rb_iter}
    (hp : heapPtrValid h p) :
    hVal (heapUpdate h p v) p = v :=
  hVal_heapUpdate_same h p v (heapPtrValid_bound hp)

-- The invariant for the while loop
private def skipInv (s : ProgramState) : Prop :=
  heapPtrValid s.globals.rawHeap s.locals.iter ∧
  LinkedListValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.iter).current


attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem rb_iter_skip_validHoare :
    rb_iter_skip_spec_ext.satisfiedBy RingBufferExt.l1_rb_iter_skip_body := by
  unfold FuncSpec.satisfiedBy rb_iter_skip_spec_ext
  -- Outer: catch BODY skip
  apply L1_hoare_catch (R := fun s => heapPtrValid s.globals.rawHeap s.locals.iter)
  · -- BODY: seq INIT (seq LOOP TEARDOWN)
    apply L1_hoare_seq (R := skipInv)
    · -- INIT: modify (skipped := 0) — only changes locals.skipped
      intro s ⟨hiter, hll⟩
      constructor
      · intro hf; exact hf
      · intro r s₁ hmem
        have ⟨hr, hs⟩ := Prod.mk.inj hmem; subst hr; subst hs
        show skipInv _; exact ⟨hiter, hll⟩
    · -- seq LOOP TEARDOWN
      apply L1_hoare_seq (R := fun s => heapPtrValid s.globals.rawHeap s.locals.iter)
      · -- LOOP: while (skipped < n) LOOP_BODY
        apply L1_hoare_while_from_body (I := skipInv)
        · -- Loop body
          -- body = seq (condition ...) (seq (seq guard (seq guard modify)) (seq (condition ...) (modify)))
          -- Split: condition check, then the rest
          apply L1_hoare_seq
            (P := fun s => skipInv s ∧ decide (s.locals.skipped < s.locals.n) = true)
            (R := fun s =>
              heapPtrValid s.globals.rawHeap s.locals.iter ∧
              (hVal s.globals.rawHeap s.locals.iter).current ≠ Ptr.null ∧
              heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.iter).current ∧
              LinkedListValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.iter).current)
          · -- COND_CHECK: condition (current == null) (modify ret + throw) skip
            apply L1_hoare_condition
            · -- True: current == null → modify ret + throw → error
              apply L1_hoare_modify_throw_catch
              -- modify only changes ret_val in locals, heapPtrValid iter preserved
              intro s ⟨⟨⟨hiter, _⟩, _⟩, _⟩
              exact hiter
            · -- False: current ≠ null → skip
              intro s₀ ⟨⟨⟨hiter, hll⟩, _⟩, hcond⟩
              simp only [decide_eq_false_iff_not] at hcond
              constructor
              · intro hf; exact hf
              · intro r s₁ hmem
                have ⟨hr, hs⟩ := Prod.mk.inj hmem; subst hr; subst hs
                exact ⟨hiter, hcond, hll.heapValid hcond, hll⟩
          · -- REST: seq ADVANCE (seq DECR_REM INC_SKIP)
            -- ADVANCE = seq (guard iterV) (seq (guard curV) (modify heap: iter.current := current.next))
            apply L1_hoare_seq_ok
              (R := fun s =>
                heapPtrValid s.globals.rawHeap s.locals.iter ∧
                LinkedListValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.iter).current)
            · -- ADVANCE
              apply L1_hoare_seq_ok
                (R := fun s =>
                  heapPtrValid s.globals.rawHeap s.locals.iter ∧
                  (hVal s.globals.rawHeap s.locals.iter).current ≠ Ptr.null ∧
                  heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.iter).current ∧
                  LinkedListValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.iter).current)
              · -- guard iterV
                apply L1_hoare_pre
                  (P := fun s =>
                    heapPtrValid s.globals.rawHeap s.locals.iter ∧
                    (heapPtrValid s.globals.rawHeap s.locals.iter ∧
                     (hVal s.globals.rawHeap s.locals.iter).current ≠ Ptr.null ∧
                     heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.iter).current ∧
                     LinkedListValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.iter).current))
                · intro s ⟨hiter, hne, hcurv, hll⟩; exact ⟨hiter, hiter, hne, hcurv, hll⟩
                · exact L1_hoare_guard' _ _
              · -- seq (guard curV) (modify heap: iter.current := current.next)
                apply L1_hoare_guard_modify_fused
                · intro s ⟨hiter, _, hcurv, _⟩; exact hcurv
                · -- After guard+modify, need to show:
                  -- 1. heapPtrValid new_heap iter (preserved)
                  -- 2. LinkedListValid new_heap (hVal new_heap iter).current
                  -- new_heap = heapUpdate old_heap iter {current := current.next, remaining := old.remaining}
                  -- hVal new_heap iter = {current := current.next, remaining := old.remaining}
                  -- So (hVal new_heap iter).current = current.next
                  -- LinkedListValid new_heap current.next = LinkedListValid old_heap current.next (types differ)
                  -- = tail of hll (since current ≠ null)
                  intro s ⟨hiter, hne, _, hll⟩
                  dsimp only
                  constructor; · rfl
                  have hiter' := heapUpdate_preserves_heapPtrValid s.globals.rawHeap s.locals.iter
                    (⟨(hVal s.globals.rawHeap (hVal s.globals.rawHeap s.locals.iter).current).next,
                      (hVal s.globals.rawHeap s.locals.iter).remaining⟩ : C_rb_iter)
                    s.locals.iter hiter
                  constructor
                  · exact hiter'
                  · rw [hVal_update_self hiter]
                    dsimp only
                    exact LinkedListValid_heapUpdate_iter hiter (hll.tail hne)
            · -- seq DECR_REM INC_SKIP
              apply L1_hoare_seq_ok
                (R := fun s =>
                  heapPtrValid s.globals.rawHeap s.locals.iter ∧
                  LinkedListValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.iter).current)
              · -- DECR_REM: condition (remaining > 0) (guard; guard; modify) skip
                apply L1_hoare_condition
                · -- True: remaining > 0 → guard iter; guard iter; modify (remaining -= 1)
                  apply L1_hoare_guard_guard_modify_fused
                  · intro s ⟨⟨hiter, _⟩, _⟩; exact hiter
                  · intro s ⟨⟨hiter, hll⟩, _⟩
                    dsimp only
                    have hiter' := heapUpdate_preserves_heapPtrValid s.globals.rawHeap s.locals.iter
                      (⟨(hVal s.globals.rawHeap s.locals.iter).current,
                        (hVal s.globals.rawHeap s.locals.iter).remaining - 1⟩ : C_rb_iter)
                      s.locals.iter hiter
                    constructor; · rfl
                    constructor
                    · exact hiter'
                    · rw [hVal_update_self hiter]
                      dsimp only
                      exact LinkedListValid_heapUpdate_iter hiter hll
                · -- False: remaining = 0 → skip
                  intro s₀ ⟨⟨hiter, hll⟩, _⟩
                  constructor
                  · intro hf; exact hf
                  · intro r s₁ hmem
                    have ⟨hr, hs⟩ := Prod.mk.inj hmem; subst hr; subst hs
                    exact ⟨rfl, hiter, hll⟩
              · -- INC_SKIP: modify (skipped += 1)
                intro s ⟨hiter, hll⟩
                constructor
                · intro hf; exact hf
                · intro r s₁ hmem
                  have ⟨hr, hs⟩ := Prod.mk.inj hmem; subst hr; subst hs
                  show skipInv _; exact ⟨hiter, hll⟩
        · -- while exit: skipInv + cond false → iterValid
          intro s ⟨hiter, _⟩ _; exact hiter
      · -- TEARDOWN: modify ret + throw — always produces error with heapPtrValid iter preserved
        intro s hiter
        constructor
        · -- ¬failed: modify+throw never fails
          intro hf
          change (_ ∨ _) at hf
          rcases hf with hf1 | ⟨s', hs', hf2⟩
          · exact hf1
          · exact hf2
        · intro r s₁ hmem
          -- results of modify+throw = {(error, f s)}
          change (_ ∨ _) at hmem
          rcases hmem with ⟨s', hs', hthr⟩ | ⟨herr, _⟩
          · have ⟨_, hs'_eq⟩ := Prod.mk.inj hs'; subst hs'_eq
            -- hthr : (r, s₁) ∈ (throw s').results = {(error, s')}
            have ⟨hr, hs₁⟩ := Prod.mk.inj hthr; subst hr; subst hs₁
            exact hiter
          · exact absurd (Prod.mk.inj herr).1 (by intro h; cases h)
  · -- Handler: skip
    intro s hiter
    constructor
    · intro hf; exact hf
    · intro r s₁ hmem
      have ⟨hr, hs⟩ := Prod.mk.inj hmem; subst hr; subst hs
      intro _; exact hiter
