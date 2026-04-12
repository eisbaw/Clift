-- Proof for rb_check_integrity_validHoare using L1_hoare_dynCom_call (TASK-0235)
--
-- rb_check_integrity calls rb_count_nodes via dynCom, then checks various
-- integrity conditions. Every path sets ret__val ∈ {0,1} and throws.
-- The outer catch+skip converts all throws to ok results.
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

-- Key lemma: rb_count_nodes only produces ok results
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
    · -- DYNCOM + CALL: uses L1_hoare_dynCom_call
      apply L1_hoare_dynCom_call
        (body := l1_rb_count_nodes_body)
        (R := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧
                        LinkedListValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
        (Q_callee := fun r _ => r = Except.ok ())
      · simp [L1.L1ProcEnv.insert]  -- lookup
      · intro s₀ ⟨h_hp, h_ll⟩; exact ⟨h_hp, h_ll⟩  -- setup preserves pre
      · exact rb_count_nodes_ok_hoare  -- callee spec
      · intro _ _ _ _; trivial  -- restore ok
      · intro _ _ _ h_eq; exact absurd h_eq (by intro h; cases h)  -- error impossible
    · -- CONDITIONALS: from True, all paths produce error with ret_val ∈ {0,1}
      -- The postcondition is: match r with | ok => spec_post | error => ret ∈ {0,1}
      -- Since all paths throw, ok case is vacuous.
      -- Prove directly at the validHoare level.
      intro s₀ _
      -- All conditionals are decidable, so they don't fail.
      -- We trace through each seq/condition at the NondetM level.
      -- The result type for the whole conditional block:
      --   ok never happens (every path ends in throw)
      --   error with ret_val ∈ {0,1}
      constructor
      · -- not failed: all conditions are decidable (decide), modify/throw/skip don't fail
        intro hf
        -- The conditionals block is a sequence of condition/modify/throw/skip.
        -- None of these can fail (conditions are deterministic, modify/throw/skip don't fail).
        -- L1.condition, L1.modify, L1.throw, L1.skip never produce failed = True.
        -- L1.seq propagates failure only from its components.
        -- We prove this by chasing through the seq structure.
        -- This is tedious but each step is simple.
        change (_ ∨ _) at hf
        rcases hf with hf1 | ⟨s1, h_cond1_ok, hf_rest⟩
        · -- first condition fails: impossible (condition uses decide, never fails)
          simp only [L1.condition] at hf1
          split at hf1 <;> exact hf1
        · change (_ ∨ _) at hf_rest
          rcases hf_rest with hf2 | ⟨s2, h_cond2_ok, hf_rest2⟩
          · -- second condition group fails
            simp only [L1.condition] at hf2
            split at hf2
            · -- count = 0 branch: seq of two conditions
              change (_ ∨ _) at hf2
              rcases hf2 with hf2a | ⟨s2a, _, hf2b⟩
              · simp only [L1.condition] at hf2a; split at hf2a <;> exact hf2a
              · simp only [L1.condition] at hf2b; split at hf2b <;> exact hf2b
            · exact hf2  -- skip: failed = False
          · change (_ ∨ _) at hf_rest2
            rcases hf_rest2 with hf3 | ⟨s3, h_cond3_ok, hf_rest3⟩
            · -- third condition group fails
              simp only [L1.condition] at hf3
              split at hf3
              · change (_ ∨ _) at hf3
                rcases hf3 with hf3a | ⟨s3a, _, hf3b⟩
                · simp only [L1.condition] at hf3a; split at hf3a <;> exact hf3a
                · simp only [L1.condition] at hf3b; split at hf3b <;> exact hf3b
              · exact hf3  -- skip: failed = False
            · -- modify(ret=1);throw fails: impossible
              exact hf_rest3
      · -- postcondition: all results have ret_val ∈ {0,1}
        intro r s₁ h_mem
        -- Chase through the seq/condition structure
        -- Each seq: ok from first goes to second, error propagates
        -- Each condition: true branch -> modify+throw (error with ret=0), false branch -> skip (ok)
        -- Final: modify(ret=1)+throw (error with ret=1)
        change (_ ∨ _) at h_mem
        rcases h_mem with ⟨s1, h_cond1, h_rest⟩ | ⟨h_cond1_err, h_eq⟩
        · -- ok from cond1 (skip case: actual = count), continue to rest
          change (_ ∨ _) at h_rest
          rcases h_rest with ⟨s2, h_cond2, h_rest2⟩ | ⟨h_cond2_err, h_eq2⟩
          · -- ok from cond2_group (skip cases), continue
            change (_ ∨ _) at h_rest2
            rcases h_rest2 with ⟨s3, h_cond3, h_rest3⟩ | ⟨h_cond3_err, h_eq3⟩
            · -- ok from cond3_group (skip cases), final modify+throw
              -- h_rest3 is in (modify(ret=1);throw s3).results
              change (_ ∨ _) at h_rest3
              rcases h_rest3 with ⟨s4, h_mod, h_throw⟩ | ⟨h_err, h_eq4⟩
              · -- ok from modify → throw: throw produces error, not ok
                exact absurd (Prod.mk.inj h_throw).1 (by intro h; cases h)
              · -- error from modify: impossible (modify only produces ok)
                exact absurd (Prod.mk.inj h_err).1 (by intro h; cases h)
            · -- error from cond3_group
              -- cond3: condition (count≠0) (seq (cond head=null → ret0;throw | skip) (cond tail=null → ret0;throw | skip)) skip
              -- Error can come from one of the inner modify+throw
              have : r = Except.error () := h_eq3
              rw [this]
              -- s₁ is the error state from the condition group
              -- Need: s₁.locals.ret__val = 0 ∨ ... = 1
              -- The error comes from modify(ret=0);throw in one of the inner conditions
              simp only [L1.condition] at h_cond3_err
              split at h_cond3_err
              · -- count ≠ 0: seq of two conditions
                change (_ ∨ _) at h_cond3_err
                rcases h_cond3_err with ⟨s3a, h_inner1, h_inner2⟩ | ⟨h_inner_err, _⟩
                · -- ok from first inner cond, then error from second inner cond
                  -- Second inner cond: modify(ret=0);throw produces (error, {... ret=0 ...})
                  simp only [L1.condition] at h_inner2
                  split at h_inner2
                  · -- tail = null: modify(ret=0);throw
                    change (_ ∨ _) at h_inner2
                    rcases h_inner2 with ⟨s3b, h_mod, _⟩ | ⟨h_err2, _⟩
                    · exact absurd (Prod.mk.inj h_mod).1 (by intro h; cases h)
                    · have ⟨_, hs₁⟩ := Prod.mk.inj h_err2; subst hs₁
                      left; rfl
                  · -- tail ≠ null: skip produces ok, not error
                    exact absurd (Prod.mk.inj h_inner2).1 (by intro h; cases h)
                · -- error from first inner cond
                  simp only [L1.condition] at h_inner_err
                  split at h_inner_err
                  · -- head = null: modify(ret=0);throw
                    change (_ ∨ _) at h_inner_err
                    rcases h_inner_err with ⟨_, h_mod, _⟩ | ⟨h_err2, _⟩
                    · exact absurd (Prod.mk.inj h_mod).1 (by intro h; cases h)
                    · have ⟨_, hs₁⟩ := Prod.mk.inj h_err2; subst hs₁
                      left; rfl
                  · -- head ≠ null: skip, ok only
                    exact absurd (Prod.mk.inj h_inner_err).1 (by intro h; cases h)
              · -- count = 0: skip, ok only (but we're in error case)
                exact absurd (Prod.mk.inj h_cond3_err).1 (by intro h; cases h)
          · -- error from cond2_group
            have : r = Except.error () := h_eq2
            rw [this]
            simp only [L1.condition] at h_cond2_err
            split at h_cond2_err
            · -- count = 0: seq of two conditions
              change (_ ∨ _) at h_cond2_err
              rcases h_cond2_err with ⟨s2a, h_inner1, h_inner2⟩ | ⟨h_inner_err, _⟩
              · simp only [L1.condition] at h_inner2
                split at h_inner2
                · change (_ ∨ _) at h_inner2
                  rcases h_inner2 with ⟨_, h_mod, _⟩ | ⟨h_err2, _⟩
                  · exact absurd (Prod.mk.inj h_mod).1 (by intro h; cases h)
                  · have ⟨_, hs₁⟩ := Prod.mk.inj h_err2; subst hs₁; left; rfl
                · exact absurd (Prod.mk.inj h_inner2).1 (by intro h; cases h)
              · simp only [L1.condition] at h_inner_err
                split at h_inner_err
                · change (_ ∨ _) at h_inner_err
                  rcases h_inner_err with ⟨_, h_mod, _⟩ | ⟨h_err2, _⟩
                  · exact absurd (Prod.mk.inj h_mod).1 (by intro h; cases h)
                  · have ⟨_, hs₁⟩ := Prod.mk.inj h_err2; subst hs₁; left; rfl
                · exact absurd (Prod.mk.inj h_inner_err).1 (by intro h; cases h)
            · -- count ≠ 0: skip, ok only
              exact absurd (Prod.mk.inj h_cond2_err).1 (by intro h; cases h)
        · -- error from cond1 (actual ≠ count: modify(ret=0);throw)
          have : r = Except.error () := h_eq
          rw [this]
          -- cond1: condition (actual ≠ count) (modify(ret=0);throw) skip
          simp only [L1.condition] at h_cond1_err
          split at h_cond1_err
          · -- actual ≠ count: modify(ret=0);throw
            change (_ ∨ _) at h_cond1_err
            rcases h_cond1_err with ⟨_, h_mod, _⟩ | ⟨h_err, _⟩
            · exact absurd (Prod.mk.inj h_mod).1 (by intro h; cases h)
            · have ⟨_, hs₁⟩ := Prod.mk.inj h_err; subst hs₁; left; rfl
          · -- actual = count: skip, ok only
            exact absurd (Prod.mk.inj h_cond1_err).1 (by intro h; cases h)
  · -- HANDLER (skip): from R, skip gives Q
    intro s hR
    exact ⟨not_false, fun r s' h_mem => by
      have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
      intro _; exact ⟨hR, rfl⟩⟩
