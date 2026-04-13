-- Proof for rb_push_if_not_full_validHoare
-- Inter-procedural: calls rb_push via dynCom pattern
-- Template: rb_check_integrity_validHoare in RBExtProofRbCheckIntegrity.lean
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
  l1_rb_fill_body l1_rb_check_integrity_body

-- Key lemma: rb_push only produces ok results (it's catch+skip)
private theorem rb_push_results_ok (s : ProgramState) :
    ∀ r s', (r, s') ∈ (l1_rb_push_body s).results → r = Except.ok () := by
  unfold l1_rb_push_body; exact L1_catch_skip_ok_only _ s

-- Callee validHoare: rb_push with ok-only postcondition.
private theorem rb_push_ok_hoare :
    validHoare
      (fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧
                heapPtrValid s.globals.rawHeap s.locals.node ∧
                (hVal s.globals.rawHeap s.locals.rb).count <
                  (hVal s.globals.rawHeap s.locals.rb).capacity ∧
                ((hVal s.globals.rawHeap s.locals.rb).tail ≠ Ptr.null →
                  heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).tail) ∧
                ((hVal s.globals.rawHeap s.locals.rb).tail ≠ Ptr.null →
                  ptrDisjoint s.locals.node (hVal s.globals.rawHeap s.locals.rb).tail))
      l1_rb_push_body
      (fun r _ => r = Except.ok ()) := by
  intro s hpre
  have ⟨h_nf, _⟩ := rb_push_validHoare s hpre
  exact ⟨h_nf, fun r s' h_mem => rb_push_results_ok s r s' h_mem⟩

theorem rb_push_if_not_full_validHoare :
    rb_push_if_not_full_spec.satisfiedBy RingBufferExt.l1_rb_push_if_not_full_body := by
  unfold FuncSpec.satisfiedBy rb_push_if_not_full_spec l1_rb_push_if_not_full_body
  -- Structure: catch(body, skip). All paths in body throw. catch+skip → all ok.
  -- Postcondition is just r = ok, which is structural from catch+skip.
  -- Main content: prove non-failure (memory safety).
  apply L1_hoare_catch (R := fun _ => True)
  · -- CATCH BODY: seq(cond_is_full, seq(dynCom_call, seq(cond_result, modify_throw)))
    -- Strategy: first handle the is_full condition via L1_hoare_seq,
    -- then prove the rest (dynCom + trailing code) directly at the NondetM level.
    apply L1_hoare_seq (R := fun s =>
      heapPtrValid s.globals.rawHeap s.locals.rb ∧
      heapPtrValid s.globals.rawHeap s.locals.node ∧
      ¬((hVal s.globals.rawHeap s.locals.rb).count ≥
        (hVal s.globals.rawHeap s.locals.rb).capacity) ∧
      ((hVal s.globals.rawHeap s.locals.rb).tail ≠ Ptr.null →
        heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).tail) ∧
      ((hVal s.globals.rawHeap s.locals.rb).tail ≠ Ptr.null →
        ptrDisjoint s.locals.node (hVal s.globals.rawHeap s.locals.rb).tail))
    · -- COND: count >= capacity → modify(ret=-1);throw | skip
      apply L1_hoare_condition
      · -- TRUE branch (is full): modify(ret_val = 0xFFFFFFFF) + throw
        -- modify+throw produces error. match error => True.
        intro s _
        have h := L1_modify_throw_result
          (fun s => { s with locals := { s.locals with ret__val := 4294967295 } }) s
        exact ⟨h.2, fun r s' h_mem => by rw [h.1] at h_mem; have ⟨hr, _⟩ := Prod.mk.inj h_mem; subst hr; trivial⟩
      · -- FALSE branch (not full): skip preserves state
        intro s₀ ⟨⟨h_rb, h_node, h_tail, h_disj⟩, h_not_full⟩
        refine ⟨not_false, fun r s₁ h_mem => ?_⟩
        have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
        simp only [decide_eq_false_iff_not] at h_not_full
        exact ⟨h_rb, h_node, h_not_full, h_tail, h_disj⟩
    · -- REST: seq(dynCom_call, seq(cond_result, modify_throw))
      -- Prove directly at the NondetM level (following check_integrity pattern).
      apply L1_hoare_seq (R := fun _ => True)
      · -- DYNCOM + CALL rb_push
        apply L1_hoare_dynCom_call
          (body := l1_rb_push_body)
          (R := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧
                          heapPtrValid s.globals.rawHeap s.locals.node ∧
                          (hVal s.globals.rawHeap s.locals.rb).count <
                            (hVal s.globals.rawHeap s.locals.rb).capacity ∧
                          ((hVal s.globals.rawHeap s.locals.rb).tail ≠ Ptr.null →
                            heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).tail) ∧
                          ((hVal s.globals.rawHeap s.locals.rb).tail ≠ Ptr.null →
                            ptrDisjoint s.locals.node (hVal s.globals.rawHeap s.locals.rb).tail))
          (Q_callee := fun r _ => r = Except.ok ())
        · -- lookup: l1Γ "rb_push" = some l1_rb_push_body
          simp [L1.L1ProcEnv.insert]
        · -- setup preserves precondition (setup is identity on relevant fields)
          intro s₀ ⟨h_rb, h_node, h_lt, h_tail, h_disj⟩
          -- Setup: { s.locals with rb := s.locals.rb, node := s.locals.node, val := s.locals.val }
          -- This is identity, so the precondition is preserved.
          -- We need count < capacity: ¬(count >= capacity) → count < capacity
          have h_lt' : (hVal s₀.globals.rawHeap s₀.locals.rb).count <
                        (hVal s₀.globals.rawHeap s₀.locals.rb).capacity :=
            Nat.lt_of_not_le h_lt
          exact ⟨h_rb, h_node, h_lt', h_tail, h_disj⟩
        · -- callee spec
          exact rb_push_ok_hoare
        · -- restore ok: from callee ok, establish dynCom postcondition
          -- Q for dynCom: match r with | ok => R | error => catch_Q
          -- For ok case: R = True
          intro _ _ _ _; trivial
        · -- error case: callee always returns ok, vacuous
          intro _ _ _ h_ok; exact absurd h_ok (by intro h; cases h)
      · -- seq(cond_result, modify_throw): from True, prove catch body Q
        -- All paths throw. Postcondition: match r | ok => post(ok) | error => True
        -- Since all paths throw, ok case is vacuous, error case is True.
        intro s₀ _
        constructor
        · -- non-failure
          intro hf
          change (_ ∨ _) at hf
          rcases hf with hf1 | ⟨s1, _, hf_rest⟩
          · simp only [L1.condition] at hf1
            split at hf1
            · exact (L1_modify_throw_result _ _).2 hf1
            · exact hf1
          · exact (L1_modify_throw_result _ _).2 hf_rest
        · -- postcondition: all paths produce error (every path ends in throw)
          intro r s₁ h_mem
          change (_ ∨ _) at h_mem
          rcases h_mem with ⟨s1, h_cond, h_rest⟩ | ⟨h_err, h_eq⟩
          · -- ok from condition (skip case), then seq(modify, throw)
            -- seq(modify, throw) always produces error
            change (_ ∨ _) at h_rest
            rcases h_rest with ⟨s2, _, h_throw⟩ | ⟨h_err_mod, h_eq_mod⟩
            · -- modify ok → throw: produces error
              have : r = Except.error () := (Prod.mk.inj h_throw).1
              subst this; trivial
            · -- modify error: impossible (modify only produces ok)
              exact absurd (Prod.mk.inj h_err_mod).1 (by intro h; cases h)
          · -- error from condition (modify+throw in true branch)
            have : r = Except.error () := h_eq; subst this; trivial
  · -- HANDLER (skip): from R=True, skip gives r = ok
    intro _ _
    exact ⟨not_false, fun r s' h_mem => (Prod.mk.inj h_mem).1⟩
