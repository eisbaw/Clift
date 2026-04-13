-- Proof for rb_check_integrity_validHoare using L1_hoare_dynCom_call (TASK-0235)
--
-- rb_check_integrity calls rb_count_nodes via dynCom, then checks various
-- integrity conditions. Every path sets ret__val ∈ {0,1} and throws.
-- The outer catch+skip converts all throws to ok results.
--
-- The dynCom+call part uses L1_hoare_dynCom_call (new infrastructure).
-- The conditionals part is standard case analysis (not dependent on TASK-0235).
import Examples.RBExtSpecs
import Examples.RBExtProofsLoops
set_option maxHeartbeats 51200000
set_option maxRecDepth 4096
open RingBufferExt

attribute [local irreducible] hVal heapUpdate heapPtrValid

-- Mark all l1 bodies irreducible to prevent kernel from unfolding callee bodies
attribute [local irreducible]
  l1_rb_init_body l1_rb_push_body l1_rb_pop_body l1_rb_peek_body
  l1_rb_size_body l1_rb_is_empty_body l1_rb_is_full_body l1_rb_clear_body
  l1_rb_count_nodes_body l1_rb_contains_body l1_rb_peek_back_body
  l1_rb_increment_all_body l1_rb_sum_body
  l1_rb_capacity_body l1_rb_remaining_body
  l1_rb_push_if_not_full_body l1_rb_pop_if_not_empty_body
  l1_rb_drain_to_body l1_rb_find_index_body l1_rb_nth_body
  l1_rb_remove_first_match_body l1_rb_stats_init_body
  l1_rb_stats_update_push_body l1_rb_stats_update_pop_body
  l1_rb_stats_reset_body l1_rb_stats_total_ops_body
  l1_rb_iter_init_body l1_rb_iter_has_next_body l1_rb_iter_next_body
  l1_rb_iter_skip_body l1_rb_equal_body l1_rb_swap_front_back_body
  l1_rb_min_body l1_rb_max_body l1_rb_replace_all_body
  l1_rb_reverse_body l1_rb_count_above_body l1_rb_count_at_or_below_body
  l1_rb_fill_body

/-! ## Helper: condition (modify ret=v; throw) skip in seq context

Each integrity check is: condition c (modify(ret=0);throw) skip.
In a seq context, the postcondition is a match on ok/error.
True branch → error with ret=0 (or ret=1 for final).
False branch → ok with True (fall through to next check). -/

private theorem cond_throw_or_skip
    (c : ProgramState → Bool) (v : UInt32)
    (P : ProgramState → Prop) (Q_ok : ProgramState → Prop)
    (h_val : v = 0 ∨ v = 1)
    (h_ok : ∀ s, P s → c s = false → Q_ok s) :
    validHoare P
      (L1.condition c
        (L1.seq (L1.modify (fun s => { s with locals := { s.locals with ret__val := v } })) L1.throw)
        L1.skip)
      (fun r s => match r with
        | Except.ok () => Q_ok s
        | Except.error () => s.locals.ret__val = 0 ∨ s.locals.ret__val = 1) := by
  apply L1_hoare_condition
  · -- true branch: modify(ret=v); throw
    apply L1_hoare_modify_throw_catch
    intro s ⟨_, _⟩
    cases h_val with
    | inl h => rw [rb_retval_val]; exact Or.inl h
    | inr h => rw [rb_retval_val]; exact Or.inr h
  · -- false branch: skip
    apply L1_hoare_pre (P := fun s => Q_ok s)
    · intro s ⟨hp, hc⟩; exact h_ok s hp hc
    · exact L1_hoare_skip _

-- Key lemma: rb_count_nodes only produces ok results
-- (its l1 body is L1.catch (loop) L1.skip, catch+skip converts all errors to ok)
private theorem rb_count_nodes_results_ok (s : ProgramState) :
    ∀ r s', (r, s') ∈ (l1_rb_count_nodes_body s).results → r = Except.ok () := by
  unfold l1_rb_count_nodes_body; exact L1_catch_skip_ok_only _ s

-- Callee validHoare with ok-only postcondition
private theorem rb_count_nodes_ok_hoare :
    validHoare
      (fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧
                LinkedListValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
      l1_rb_count_nodes_body
      (fun r _ => r = Except.ok ()) := by
  intro s ⟨h_hp, h_ll⟩
  have ⟨h_nf, _⟩ := rb_count_nodes_validHoare s ⟨h_hp, h_ll⟩
  exact ⟨h_nf, fun r s' h_mem => rb_count_nodes_results_ok s r s' h_mem⟩

theorem rb_check_integrity_validHoare :
    rb_check_integrity_spec.satisfiedBy RingBufferExt.l1_rb_check_integrity_body := by
  unfold FuncSpec.satisfiedBy rb_check_integrity_spec l1_rb_check_integrity_body
  apply L1_hoare_catch (R := fun s => s.locals.ret__val = 0 ∨ s.locals.ret__val = 1)
  · -- CATCH BODY: seq (dynCom_call) (conditionals)
    apply L1_hoare_seq (R := fun _ => True)
    · -- DYNCOM + CALL: uses L1_hoare_dynCom_call (TASK-0235 infrastructure)
      -- This is the key inter-procedural step: call rb_count_nodes via dynCom
      -- with save/setup/call/restore pattern, keeping the callee body OPAQUE.
      apply L1_hoare_dynCom_call
        (body := l1_rb_count_nodes_body)
        (R := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧
                        LinkedListValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
        (Q_callee := fun r _ => r = Except.ok ())
      · -- lookup: inline proc env maps "rb_count_nodes" to its l1 body
        simp [L1.L1ProcEnv.insert]
      · -- setup preserves callee precondition (identity on rb/globals)
        intro s₀ ⟨h_hp, h_ll⟩; exact ⟨h_hp, h_ll⟩
      · -- callee spec: rb_count_nodes returns ok (catch+skip)
        exact rb_count_nodes_ok_hoare
      · -- restore ok → True (trivial intermediate condition)
        intro _ _ _ _; trivial
      · -- error impossible: Q_callee says r = ok, but h says r = error
        intro _ _ _ h_eq; exact absurd h_eq (by intro h; cases h)
    · -- CONDITIONALS: from True, all paths set ret_val ∈ {0,1} and throw
      -- Structure: seq cond1 (seq cond2_group (seq cond5_group final))
      -- Each cond: condition c (modify(ret=0);throw) skip
      -- final: modify(ret=1);throw
      -- Decompose outer seq: cond1 ; rest
      apply L1_hoare_seq (R := fun _ => True)
      · -- cond1: actual ≠ count → ret=0, throw | skip
        exact cond_throw_or_skip _ 0 _ _ (Or.inl rfl) (fun _ _ _ => trivial)
      · -- rest: seq cond2_group (seq cond5_group final)
        apply L1_hoare_seq (R := fun _ => True)
        · -- cond2_group: count=0 → (seq cond3 cond4) | skip
          apply L1_hoare_condition
          · -- cond2 true: seq cond3 cond4
            apply L1_hoare_seq (R := fun _ => True)
            · -- cond3: head ≠ null → ret=0, throw | skip
              exact cond_throw_or_skip _ 0 _ _ (Or.inl rfl) (fun _ _ _ => trivial)
            · -- cond4: tail ≠ null → ret=0, throw | skip
              exact cond_throw_or_skip _ 0 _ _ (Or.inl rfl) (fun _ _ _ => trivial)
          · -- cond2 false: skip
            apply L1_hoare_pre (P := fun s => True)
            · intro s ⟨_, _⟩; trivial
            · exact L1_hoare_skip _
        · -- rest2: seq cond5_group final
          apply L1_hoare_seq (R := fun _ => True)
          · -- cond5_group: count ≠ 0 → (seq cond6 cond7) | skip
            apply L1_hoare_condition
            · -- cond5 true: seq cond6 cond7
              apply L1_hoare_seq (R := fun _ => True)
              · -- cond6: head = null → ret=0, throw | skip
                exact cond_throw_or_skip _ 0 _ _ (Or.inl rfl) (fun _ _ _ => trivial)
              · -- cond7: tail = null → ret=0, throw | skip
                exact cond_throw_or_skip _ 0 _ _ (Or.inl rfl) (fun _ _ _ => trivial)
            · -- cond5 false: skip
              apply L1_hoare_pre (P := fun s => True)
              · intro s ⟨_, _⟩; trivial
              · exact L1_hoare_skip _
          · -- final: modify(ret=1); throw
            apply L1_hoare_modify_throw_catch
            intro s _; rw [rb_retval_val]; exact Or.inr rfl
  · -- HANDLER (skip): from R (ret_val ∈ {0,1}), skip preserves state → Q
    intro s hR
    exact ⟨not_false, fun r s' h_mem => by
      have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
      intro _; exact ⟨hR, rfl⟩⟩
