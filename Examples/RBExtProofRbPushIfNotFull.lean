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
-- Uses rb_push_validHoare for non-failure, structural ok-only for postcondition.
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
  -- Structure: catch(body, skip). Body always throws. catch+skip → all results ok.
  -- Postcondition is r = ok, which follows structurally from catch+skip.
  -- Main obligation: prove non-failure (all guards in all paths succeed).
  apply L1_hoare_catch (R := fun _ => True)
  · -- CATCH BODY: seq(cond_is_full, seq(dynCom_call, seq(cond_result, modify_throw)))
    -- All paths end in throw. R = True suffices since postcondition is just r = ok.
    -- For catch body postcondition: ok results → post(ok, s) i.e. ok = ok (trivial)
    --                                error results → R s i.e. True (trivial)
    apply L1_hoare_seq
      (R := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧
                      heapPtrValid s.globals.rawHeap s.locals.node ∧
                      ¬((hVal s.globals.rawHeap s.locals.rb).count ≥
                        (hVal s.globals.rawHeap s.locals.rb).capacity) ∧
                      ((hVal s.globals.rawHeap s.locals.rb).tail ≠ Ptr.null →
                        heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).tail) ∧
                      ((hVal s.globals.rawHeap s.locals.rb).tail ≠ Ptr.null →
                        ptrDisjoint s.locals.node (hVal s.globals.rawHeap s.locals.rb).tail))
    · -- COND: count >= capacity → modify(ret=-1);throw | skip
      apply L1_hoare_condition
      · -- TRUE branch (is full): modify(ret_val = 0xFFFFFFFF) + throw → error
        -- catch body postcondition for error: R s = True
        apply L1_hoare_modify_throw (R := fun _ => True)
        intro _ _; trivial
      · -- FALSE branch (not full): skip → ok with intermediate R
        intro s ⟨⟨h_rb, h_node, _, h_tail, h_disj⟩, h_not_full⟩
        constructor
        · intro h; exact h
        · intro r s' h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
          have h_lt : ¬((hVal s.globals.rawHeap s.locals.rb).count ≥
                        (hVal s.globals.rawHeap s.locals.rb).capacity) := by
            simp only [decide_eq_false_iff_not] at h_not_full; exact h_not_full
          exact ⟨h_rb, h_node, h_lt, h_tail, h_disj⟩
    · -- REST: seq(dynCom_call, seq(cond_result, modify_throw))
      -- All paths throw, so postcondition for error is R = True.
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
        · -- setup preserves precondition (setup is identity)
          intro s₀ ⟨h_rb, h_node, h_lt, h_tail, h_disj⟩
          exact ⟨h_rb, h_node, h_lt, h_tail, h_disj⟩
        · -- callee spec
          exact rb_push_ok_hoare
        · -- restore ok: dynCom ok postcondition
          -- Q for dynCom = match r with ok => intermediate R | error => catch_error Q
          -- For ok: need intermediate R (True, since later steps handle it)
          -- Actually, the Q of the dynCom must match what L1_hoare_seq expects:
          --   match r with | ok => R s | error => catch_body_Q error s
          -- R = True, so ok case → True. Error case → True (R for catch).
          intro _ _ _ _; trivial
        · -- error case: callee always returns ok, so this is vacuous
          intro _ _ _ h_ok
          exact absurd h_ok (by intro h; cases h)
      · -- seq(cond_result, modify_throw): all paths throw, postcondition trivial
        -- From True, prove catch body postcondition (ok → post(ok) / error → R=True)
        intro s₀ _
        -- The remaining code: seq(condition(result≠0, modify+throw, skip), seq(modify, throw))
        -- All paths throw. We prove non-failure and postcondition = True.
        constructor
        · -- non-failure: condition never fails, modify never fails, throw never fails
          intro hf
          change (_ ∨ _) at hf
          rcases hf with hf1 | ⟨s1, _, hf_rest⟩
          · -- condition failure: impossible
            simp only [L1.condition] at hf1
            split at hf1
            · -- true branch: modify+throw doesn't fail
              exact (L1_modify_throw_result _ _).2 hf1
            · exact hf1  -- skip doesn't fail
          · -- rest failure: modify+throw doesn't fail
            exact (L1_modify_throw_result _ _).2 hf_rest
        · -- postcondition
          intro r s₁ h_mem
          change (_ ∨ _) at h_mem
          rcases h_mem with ⟨s1, _, h_rest⟩ | ⟨h_err, _⟩
          · -- ok from condition, then modify+throw → error → True
            change (_ ∨ _) at h_rest
            rcases h_rest with ⟨s2, _, h_throw⟩ | ⟨_, _⟩
            · exact absurd (Prod.mk.inj h_throw).1 (by intro h; cases h)
            · trivial  -- error result → R = True
          · -- error from condition → R = True
            trivial
  · -- HANDLER (skip): from R=True, skip gives post (r = ok)
    intro _ _
    exact ⟨not_false, fun r s' h_mem => by
      have ⟨hr, _⟩ := Prod.mk.inj h_mem; exact hr⟩
