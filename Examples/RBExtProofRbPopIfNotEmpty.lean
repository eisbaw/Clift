-- Proof for rb_pop_if_not_empty_validHoare
-- Inter-procedural: calls rb_pop via dynCom pattern
-- Template: rb_push_if_not_full_validHoare in RBExtProofRbPushIfNotFull.lean
import Examples.RBExtSpecs
import Examples.RBExtProofRbPop
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

-- Key lemma: rb_pop only produces ok results (it's catch+skip)
private theorem rb_pop_results_ok (s : ProgramState) :
    ∀ r s', (r, s') ∈ (l1_rb_pop_body s).results → r = Except.ok () := by
  unfold l1_rb_pop_body; exact L1_catch_skip_ok_only _ s

-- Callee validHoare: rb_pop with weak precondition.
-- Postcondition: r = ok, ret_val ∈ {0,1}, heapPtrValid rb preserved.
-- Proof: case split on head=null.
--   head=null: early return (ret=1), no guards, no failure.
--   head≠null: delegate to rb_pop_validHoare_proven (which now includes heapPtrValid rb).
private theorem rb_pop_callee_hoare :
    validHoare
      (fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧
                heapPtrValid s.globals.rawHeap s.locals.out_val ∧
                ((hVal s.globals.rawHeap s.locals.rb).head ≠ Ptr.null →
                  heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head))
      l1_rb_pop_body
      (fun r s => r = Except.ok () ∧
                  (s.locals.ret__val = 0 ∨ s.locals.ret__val = 1) ∧
                  heapPtrValid s.globals.rawHeap s.locals.rb) := by
  intro s₀ ⟨h_rb, h_ov, h_head_valid⟩
  by_cases h_head : (hVal s₀.globals.rawHeap s₀.locals.rb).head = Ptr.null
  · -- HEAD = NULL: rb_pop takes early return. ret_val := 1, throw, catch → skip → ok.
    constructor
    · -- non-failure
      intro hf; revert hf; unfold l1_rb_pop_body
      simp only [L1.catch, L1.seq, L1.condition, h_head, ↓reduceIte, L1.modify, L1.throw, L1.skip]
      intro hf; change (_ ∨ _) at hf
      rcases hf with hf1 | ⟨_, _, hf2⟩
      · change (_ ∨ _) at hf1
        rcases hf1 with hf_cond | ⟨_, h_ok, _⟩
        · change (_ ∨ _) at hf_cond
          rcases hf_cond with hf_mod | ⟨_, _, hf_throw⟩
          · exact hf_mod
          · exact hf_throw
        · change (_ ∈ ({(Except.ok (), _)} : Set _)) at h_ok
          cases (Prod.mk.inj h_ok).1
      · exact hf2
    · -- postcondition
      intro r s₁ h_mem
      have h_ok := rb_pop_results_ok s₀ r s₁ h_mem
      subst h_ok; refine ⟨rfl, ?_, ?_⟩
      all_goals {
        revert h_mem; unfold l1_rb_pop_body
        simp only [L1.catch, L1.seq, L1.condition, h_head, ↓reduceIte, L1.modify, L1.throw, L1.skip]
        intro h_mem; change (_ ∨ _) at h_mem
        rcases h_mem with ⟨h_ok_mem, _⟩ | ⟨s', h_err, h_skip⟩
        · exfalso; change (_ ∨ _) at h_ok_mem
          rcases h_ok_mem with ⟨_, h_cok, _⟩ | ⟨h_cerr, _⟩
          · change (_ ∈ ({(Except.ok (), _)} : Set _)) at h_cok; cases (Prod.mk.inj h_cok).1
          · cases h_cerr
        · have ⟨_, hs⟩ := Prod.mk.inj h_skip; subst hs
          change (_ ∨ _) at h_err
          rcases h_err with ⟨_, h_cok, _⟩ | ⟨h_cerr, _⟩
          · exfalso; change (_ ∈ ({(Except.ok (), _)} : Set _)) at h_cok; cases (Prod.mk.inj h_cok).1
          · change (_ ∨ _) at h_cerr
            rcases h_cerr with ⟨s₃, h_mod, h_throw⟩ | ⟨h_moderr, _⟩
            · have ⟨_, hs₃⟩ := Prod.mk.inj h_mod; subst hs₃
              have ⟨_, hs'⟩ := Prod.mk.inj h_throw; subst hs'
              first | exact Or.inr rfl | exact h_rb
            · exfalso; cases (Prod.mk.inj h_moderr).1
      }
  · -- HEAD ≠ NULL: use rb_pop_validHoare_proven
    have h_hv := h_head_valid h_head
    have ⟨h_nf, h_post⟩ := rb_pop_validHoare_proven s₀ ⟨h_rb, h_ov, h_head, h_hv⟩
    constructor
    · exact h_nf
    · intro r s₁ h_mem
      have h_ok := rb_pop_results_ok s₀ r s₁ h_mem
      subst h_ok; refine ⟨rfl, ?_, ?_⟩
      · have ⟨h_ret, _, _⟩ := h_post (Except.ok ()) s₁ h_mem rfl
        exact Or.inl h_ret
      · exact (h_post (Except.ok ()) s₁ h_mem rfl).2.2

theorem rb_pop_if_not_empty_validHoare :
    rb_pop_if_not_empty_spec.satisfiedBy RingBufferExt.l1_rb_pop_if_not_empty_body := by
  unfold FuncSpec.satisfiedBy rb_pop_if_not_empty_spec l1_rb_pop_if_not_empty_body
  -- Structure: catch(body, skip). Body: seq(cond(count=0, modify(ret:=1)+throw, skip),
  --   seq(dynCom(call rb_pop), seq(modify(ret_val := result), throw)))
  -- All paths in body throw. catch catches error → skip → ok.
  -- R: (ret_val = 0 ∨ ret_val = 1) ∧ heapPtrValid rb.
  apply L1_hoare_catch
    (R := fun s => (s.locals.ret__val = 0 ∨ s.locals.ret__val = 1) ∧
                    heapPtrValid s.globals.rawHeap s.locals.rb)
  · -- CATCH BODY: all paths throw. Need R at every error state.
    apply L1_hoare_seq
      (R := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧
                      heapPtrValid s.globals.rawHeap s.locals.out_val ∧
                      ¬((hVal s.globals.rawHeap s.locals.rb).count = 0) ∧
                      ((hVal s.globals.rawHeap s.locals.rb).head ≠ Ptr.null →
                        heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head))
    · -- COND: count = 0 → modify(ret:=1)+throw | skip
      apply L1_hoare_condition
      · -- TRUE branch (is empty): modify(ret_val := 1) + throw → error with R
        intro s ⟨⟨h_rb, h_ov, h_head_v⟩, _⟩
        have h := L1_modify_throw_result
          (fun s : ProgramState => { s with locals := { s.locals with ret__val := 1 } }) s
        exact ⟨h.2, fun r s' h_mem => by
          rw [h.1] at h_mem; have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
          exact ⟨Or.inr rfl, h_rb⟩⟩
      · -- FALSE branch (not empty): skip preserves state, establish intermediate R
        intro s ⟨⟨h_rb, h_ov, h_head_v⟩, h_not_empty⟩
        simp only [decide_eq_false_iff_not] at h_not_empty
        exact ⟨not_false, fun r s' h_mem => by
          have ⟨_, hs⟩ := Prod.mk.inj h_mem; subst hs
          exact ⟨h_rb, h_ov, h_not_empty, h_head_v⟩⟩
    · -- REST: seq(dynCom_call, seq(modify(ret_val := result), throw))
      -- After dynCom: result = callee_ret_val, rb = saved.rb, globals from callee.
      -- After modify(ret_val := result): ret_val = result = callee_ret_val.
      -- After throw: error → R.
      -- Intermediate R between dynCom and modify+throw:
      --   (result = 0 ∨ result = 1) ∧ heapPtrValid rb
      apply L1_hoare_seq
        (R := fun s => (s.locals.result = 0 ∨ s.locals.result = 1) ∧
                        heapPtrValid s.globals.rawHeap s.locals.rb)
      · -- DYNCOM + CALL rb_pop
        apply L1_hoare_dynCom_call
          (body := l1_rb_pop_body)
          (R := fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧
                          heapPtrValid s.globals.rawHeap s.locals.out_val ∧
                          ((hVal s.globals.rawHeap s.locals.rb).head ≠ Ptr.null →
                            heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head))
          (Q_callee := fun r s => r = Except.ok () ∧
                        (s.locals.ret__val = 0 ∨ s.locals.ret__val = 1) ∧
                        heapPtrValid s.globals.rawHeap s.locals.rb)
        · -- lookup: l1Γ "rb_pop" = some l1_rb_pop_body
          simp [L1.L1ProcEnv.insert]
        · -- setup preserves callee precondition
          intro s₀ ⟨h_rb, h_ov, _, h_head_v⟩
          exact ⟨h_rb, h_ov, h_head_v⟩
        · -- callee spec
          exact rb_pop_callee_hoare
        · -- restore ok: Q_callee ok s' → Q ok (restore saved s')
          -- restore: fun s => { s with locals := { saved.locals with result := s.locals.ret__val } }
          -- So (restore saved s').locals.result = s'.locals.ret__val (callee ret_val)
          --    (restore saved s').locals.rb = saved.locals.rb
          --    (restore saved s').globals = s'.globals
          -- Need: (result = 0 ∨ result = 1) ∧ heapPtrValid rb
          -- result = callee_ret_val ∈ {0,1} from Q_callee
          -- heapPtrValid rb: heap = s'.globals.rawHeap, rb = saved.locals.rb = s₀.locals.rb
          -- Q_callee gives heapPtrValid s'.globals.rawHeap s'.locals.rb
          -- But s'.locals.rb = setup(s₀).locals.rb = s₀.locals.rb (setup is identity on rb)
          -- So heapPtrValid s'.globals.rawHeap s₀.locals.rb = heapPtrValid s'.globals.rawHeap s'.locals.rb ✓
          -- And after restore: globals = s'.globals, rb = saved.locals.rb = s₀.locals.rb.
          -- So heapPtrValid (restore saved s').globals.rawHeap (restore saved s').locals.rb
          --  = heapPtrValid s'.globals.rawHeap s₀.locals.rb
          --  = heapPtrValid s'.globals.rawHeap s'.locals.rb (since s'.locals.rb = s₀.locals.rb)
          -- This follows from Q_callee.
          -- For the result: (restore saved s').locals.result = s'.locals.ret__val
          -- Q_callee gives: s'.locals.ret__val = 0 ∨ s'.locals.ret__val = 1
          -- For Q ok case: match ok | ok => R | error => ... → R
          -- R = (result ∈ {0,1}) ∧ heapPtrValid rb
          intro s₀ s' ⟨h_rb, h_ov, _, h_head_v⟩ ⟨_, h_ret_01, h_rb'⟩
          -- Q ok (restore s₀ s') matches the ok branch of catch body Q
          -- We're in the ok arm: need R_seq (intermediate between dynCom and modify+throw)
          -- Actually, looking at L1_hoare_dynCom_call signature:
          -- h_restore : ∀ s₀ s', P s₀ → Q_callee ok s' → Q ok (restore s₀ s')
          -- Q here is the postcondition of the dynCom (from the enclosing L1_hoare_seq)
          -- which is: match r | ok => seq_mid_R | error => catch_body_error_Q
          -- For ok: seq_mid_R (restore s₀ s')
          --   = (result = 0 ∨ result = 1) ∧ heapPtrValid rb
          -- where result = s'.locals.ret__val (from restore)
          -- and rb = s₀.locals.rb, heap = s'.globals.rawHeap (from restore)
          constructor
          · -- result = 0 ∨ result = 1
            exact h_ret_01
          · -- heapPtrValid rb
            exact h_rb'
        · -- error case: callee always returns ok, vacuous
          intro _ _ _ ⟨h_ok, _⟩; exact absurd h_ok (by intro h; cases h)
      · -- modify(ret_val := result) + throw: from intermediate R, establish catch body Q
        -- R_mid: (result = 0 ∨ result = 1) ∧ heapPtrValid rb
        -- modify sets ret_val := result. throw produces error.
        -- catch body Q: match error => R_catch = (ret_val ∈ {0,1} ∧ heapPtrValid rb)
        -- After modify: ret_val = result ∈ {0,1}. heapPtrValid rb unchanged (no heap change).
        intro s₀ ⟨h_result_01, h_rb⟩
        have h := L1_modify_throw_result
          (fun s : ProgramState => { s with locals := { s.locals with ret__val := s.locals.result } }) s₀
        exact ⟨h.2, fun r s' h_mem => by
          rw [h.1] at h_mem; have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
          exact ⟨h_result_01, h_rb⟩⟩
  · -- HANDLER (skip): from R, establish postcondition
    -- R: (ret_val ∈ {0,1}) ∧ heapPtrValid rb
    -- Post: r = ok → (ret_val ∈ {0,1}) ∧ heapPtrValid rb
    intro s ⟨h_ret, h_rb⟩
    exact ⟨not_false, fun r s' h_mem => by
      have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
      intro _; exact ⟨h_ret, h_rb⟩⟩
