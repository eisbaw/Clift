-- Proven (sorry-free) validHoare proofs: rb_push + traversal loop proofs.
-- Split from RBExtFuncSpecs.lean (task 0233).
--
-- Contents:
--   rb_push_validHoare          (complex heap mutation, sorry-free)
--   rb_count_nodes_validHoare   (loop traversal)
--   rb_contains_validHoare      (loop traversal)
--   rb_find_index_validHoare    (loop traversal)
--   rb_nth_validHoare           (loop traversal)
--   rb_sum_validHoare           (loop traversal)

import Examples.RBExtSpecs

set_option maxHeartbeats 12800000
set_option maxRecDepth 4096

open RingBufferExt

/-! # validHoare proofs: stated for all 40, sorry for complex ones

    The 18 existing specs from RingBufferExtProof.lean already have some proofs
    (or at least specs). Here we state theorems for ALL 40 functions.
    The proof score is measured below. -/

-- Category A: read-only accessors (already have specs in RingBufferExtProof.lean)
-- validHoare proofs for these are straightforward but not yet done.
-- Using the existing specs from RingBufferExtProof.lean:

/-! ## rb_push validHoare proof

    Proof strategy: Hoare-level decomposition.
    - L1_hoare_catch at the outer level
    - L1_hoare_condition for the count>=cap check (false branch)
    - Chain of L1_hoare_seq_ok / L1_hoare_guard_modify_fused for heap steps
    - L1_hoare_condition for the two inner conditionals (tail≠null, head=null)
    - Final modify+throw handled by the catch→skip handler

    Heap frame reasoning:
    - rb (C_rb_state) vs node (C_rb_node): different type tags → ptrDisjoint
    - node vs tail: from precondition (when tail ≠ null)
    - heapUpdate_preserves_heapPtrValid for validity through updates -/

set_option maxRecDepth 8192 in
set_option maxHeartbeats 51200000 in
theorem rb_push_validHoare :
    rb_push_spec.satisfiedBy RingBufferExt.l1_rb_push_body := by
  unfold FuncSpec.satisfiedBy rb_push_spec
  -- Use Hoare-level decomposition. Add `dsimp only` to reduce generated state projections.
  apply L1_hoare_catch (R := fun s =>
    s.locals.ret__val = 0 ∧
    (hVal s.globals.rawHeap s.locals.node).value = s.locals.val ∧
    (hVal s.globals.rawHeap s.locals.rb).tail = s.locals.node ∧
    (hVal s.globals.rawHeap s.locals.node).next = Ptr.null)
  · -- Body: seq(cond, rest). cond false→skip, rest ends with throw.
    apply L1_hoare_seq (R := fun s =>
      heapPtrValid s.globals.rawHeap s.locals.rb ∧
      heapPtrValid s.globals.rawHeap s.locals.node ∧
      (hVal s.globals.rawHeap s.locals.rb).count <
        (hVal s.globals.rawHeap s.locals.rb).capacity ∧
      ((hVal s.globals.rawHeap s.locals.rb).tail ≠ Ptr.null →
        heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).tail) ∧
      ((hVal s.globals.rawHeap s.locals.rb).tail ≠ Ptr.null →
        ptrDisjoint s.locals.node (hVal s.globals.rawHeap s.locals.rb).tail))
    · -- cond_check: condition(count>=cap, ret1+throw, skip)
      apply L1_hoare_condition
      · -- True: count>=cap contradicts count<cap
        intro s ⟨⟨_, _, hlt', _, _⟩, hcond⟩
        simp only [decide_eq_true_eq] at hcond
        exact absurd hlt' (Nat.not_lt.mpr hcond)
      · -- False: skip preserves state
        intro s ⟨⟨hrb', hnode', hlt', htv, htd⟩, _⟩
        constructor
        · intro hf; exact hf
        · intro r s' hmem
          have ⟨hr, hs⟩ := Prod.mk.inj hmem; subst hr; subst hs
          exact ⟨hrb', hnode', hlt', htv, htd⟩
    · -- rest: guard+modify chain ending in throw
      -- Step 1: guard(nodeV) ; modify(node.value := val)
      apply L1_hoare_seq_ok (R := fun s =>
        heapPtrValid s.globals.rawHeap s.locals.rb ∧
        heapPtrValid s.globals.rawHeap s.locals.node ∧
        (hVal s.globals.rawHeap s.locals.node).value = s.locals.val ∧
        ((hVal s.globals.rawHeap s.locals.rb).tail ≠ Ptr.null →
          heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).tail) ∧
        ((hVal s.globals.rawHeap s.locals.rb).tail ≠ Ptr.null →
          ptrDisjoint s.locals.node (hVal s.globals.rawHeap s.locals.rb).tail))
      · apply L1_hoare_guard_modify_fused
        · intro s ⟨_, hnode', _, _, _⟩; exact hnode'
        · intro s ⟨hrb', hnode', _, htv, htd⟩; dsimp only; constructor; · rfl
          have hbn := heapPtrValid_bound hnode'
          have hbr := heapPtrValid_bound hrb'
          refine ⟨heapUpdate_preserves_heapPtrValid _ _ _ _ hrb',
                  heapUpdate_preserves_heapPtrValid _ _ _ _ hnode', ?_, ?_, ?_⟩
          · rw [hVal_heapUpdate_same _ _ _ hbn]
          · intro h
            have h_disj := ptrDisjoint_symm (rb_node_disjoint hrb' hnode')
            rw [hVal_heapUpdate_disjoint _ _ _ _ hbn hbr h_disj] at h
            rw [hVal_heapUpdate_disjoint _ _ _ _ hbn hbr h_disj]
            exact heapUpdate_preserves_heapPtrValid _ _ _ _ (htv h)
          · intro h
            have h_disj := ptrDisjoint_symm (rb_node_disjoint hrb' hnode')
            rw [hVal_heapUpdate_disjoint _ _ _ _ hbn hbr h_disj] at h
            rw [hVal_heapUpdate_disjoint _ _ _ _ hbn hbr h_disj]
            exact htd h
      · -- Step 2: guard(nodeV) ; modify(node.next := null)
        apply L1_hoare_seq_ok (R := fun s =>
          heapPtrValid s.globals.rawHeap s.locals.rb ∧
          heapPtrValid s.globals.rawHeap s.locals.node ∧
          (hVal s.globals.rawHeap s.locals.node).value = s.locals.val ∧
          (hVal s.globals.rawHeap s.locals.node).next = Ptr.null ∧
          ((hVal s.globals.rawHeap s.locals.rb).tail ≠ Ptr.null →
            heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).tail) ∧
          ((hVal s.globals.rawHeap s.locals.rb).tail ≠ Ptr.null →
            ptrDisjoint s.locals.node (hVal s.globals.rawHeap s.locals.rb).tail))
        · apply L1_hoare_guard_modify_fused
          · intro s ⟨_, hnode', _, _, _⟩; exact hnode'
          · intro s ⟨hrb', hnode', hval, htv, htd⟩; dsimp only; constructor; · rfl
            have hbn := heapPtrValid_bound hnode'
            have hbr := heapPtrValid_bound hrb'
            refine ⟨heapUpdate_preserves_heapPtrValid _ _ _ _ hrb',
                    heapUpdate_preserves_heapPtrValid _ _ _ _ hnode', ?_, ?_, ?_, ?_⟩
            · rw [hVal_heapUpdate_same _ _ _ hbn]; exact hval
            · rw [hVal_heapUpdate_same _ _ _ hbn]
            · intro h
              have h_disj := ptrDisjoint_symm (rb_node_disjoint hrb' hnode')
              rw [hVal_heapUpdate_disjoint _ _ _ _ hbn hbr h_disj] at h
              rw [hVal_heapUpdate_disjoint _ _ _ _ hbn hbr h_disj]
              exact heapUpdate_preserves_heapPtrValid _ _ _ _ (htv h)
            · intro h
              have h_disj := ptrDisjoint_symm (rb_node_disjoint hrb' hnode')
              rw [hVal_heapUpdate_disjoint _ _ _ _ hbn hbr h_disj] at h
              rw [hVal_heapUpdate_disjoint _ _ _ _ hbn hbr h_disj]
              exact htd h
        · -- Step 3: cond(tail≠null, guard(tailV);modify(tail.next:=node), skip)
          apply L1_hoare_seq_ok (R := fun s =>
            heapPtrValid s.globals.rawHeap s.locals.rb ∧
            heapPtrValid s.globals.rawHeap s.locals.node ∧
            (hVal s.globals.rawHeap s.locals.node).value = s.locals.val ∧
            (hVal s.globals.rawHeap s.locals.node).next = Ptr.null)
          · apply L1_hoare_condition'
            · -- True: tail≠null
              apply L1_hoare_pre (P := fun s =>
                heapPtrValid s.globals.rawHeap s.locals.rb ∧
                heapPtrValid s.globals.rawHeap s.locals.node ∧
                (hVal s.globals.rawHeap s.locals.node).value = s.locals.val ∧
                (hVal s.globals.rawHeap s.locals.node).next = Ptr.null ∧
                heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).tail ∧
                ptrDisjoint s.locals.node (hVal s.globals.rawHeap s.locals.rb).tail)
              · intro s ⟨⟨hrb', hnode', hval, hnxt, htv, htd⟩, hcond⟩
                simp only [decide_eq_true_eq] at hcond
                exact ⟨hrb', hnode', hval, hnxt, htv hcond, htd hcond⟩
              · apply L1_hoare_guard_modify_fused
                · intro s ⟨_, _, _, _, htv, _⟩; exact htv
                · intro s ⟨hrb', hnode', hval, hnxt, htv, htd⟩; dsimp only; constructor; · rfl
                  have hbt := heapPtrValid_bound htv
                  have hbn := heapPtrValid_bound hnode'
                  refine ⟨heapUpdate_preserves_heapPtrValid _ _ _ _ hrb',
                          heapUpdate_preserves_heapPtrValid _ _ _ _ hnode', ?_, ?_⟩
                  · rw [hVal_heapUpdate_disjoint _ _ _ _ hbt hbn (ptrDisjoint_symm htd)]; exact hval
                  · rw [hVal_heapUpdate_disjoint _ _ _ _ hbt hbn (ptrDisjoint_symm htd)]; exact hnxt
            · -- False: tail=null, skip
              apply L1_hoare_pre (P := fun s =>
                heapPtrValid s.globals.rawHeap s.locals.rb ∧
                heapPtrValid s.globals.rawHeap s.locals.node ∧
                (hVal s.globals.rawHeap s.locals.node).value = s.locals.val ∧
                (hVal s.globals.rawHeap s.locals.node).next = Ptr.null)
              · intro s ⟨⟨hrb', hnode', hval, hnxt, _, _⟩, _⟩
                exact ⟨hrb', hnode', hval, hnxt⟩
              · intro s hR; constructor
                · intro hf; exact hf
                · intro r s' hmem; have ⟨hr, hs⟩ := Prod.mk.inj hmem; subst hr; subst hs
                  exact ⟨rfl, hR⟩
          · -- Step 4: guard(rbV);modify(rb.tail:=node)
            apply L1_hoare_seq_ok (R := fun s =>
              heapPtrValid s.globals.rawHeap s.locals.rb ∧
              heapPtrValid s.globals.rawHeap s.locals.node ∧
              (hVal s.globals.rawHeap s.locals.node).value = s.locals.val ∧
              (hVal s.globals.rawHeap s.locals.node).next = Ptr.null ∧
              (hVal s.globals.rawHeap s.locals.rb).tail = s.locals.node)
            · apply L1_hoare_guard_modify_fused
              · intro s ⟨hrb', _, _, _⟩; exact hrb'
              · intro s ⟨hrb', hnode', hval, hnxt⟩; dsimp only; constructor; · rfl
                have hbr := heapPtrValid_bound hrb'
                have hbn := heapPtrValid_bound hnode'
                refine ⟨heapUpdate_preserves_heapPtrValid _ _ _ _ hrb',
                        heapUpdate_preserves_heapPtrValid _ _ _ _ hnode', ?_, ?_, ?_⟩
                · rw [hVal_heapUpdate_disjoint _ _ _ _ hbr hbn (rb_node_disjoint hrb' hnode')]; exact hval
                · rw [hVal_heapUpdate_disjoint _ _ _ _ hbr hbn (rb_node_disjoint hrb' hnode')]; exact hnxt
                · rw [hVal_heapUpdate_same _ _ _ hbr]
            · -- Step 5: cond(head=null, guard(rbV);modify(rb.head:=node), skip)
              apply L1_hoare_seq_ok (R := fun s =>
                heapPtrValid s.globals.rawHeap s.locals.rb ∧
                heapPtrValid s.globals.rawHeap s.locals.node ∧
                (hVal s.globals.rawHeap s.locals.node).value = s.locals.val ∧
                (hVal s.globals.rawHeap s.locals.node).next = Ptr.null ∧
                (hVal s.globals.rawHeap s.locals.rb).tail = s.locals.node)
              · apply L1_hoare_condition'
                · -- True: head=null
                  apply L1_hoare_pre (P := fun s =>
                    heapPtrValid s.globals.rawHeap s.locals.rb ∧
                    heapPtrValid s.globals.rawHeap s.locals.node ∧
                    (hVal s.globals.rawHeap s.locals.node).value = s.locals.val ∧
                    (hVal s.globals.rawHeap s.locals.node).next = Ptr.null ∧
                    (hVal s.globals.rawHeap s.locals.rb).tail = s.locals.node)
                  · intro s ⟨hpre, _⟩; exact hpre
                  · apply L1_hoare_guard_modify_fused
                    · intro s ⟨hrb', _, _, _, _⟩; exact hrb'
                    · intro s ⟨hrb', hnode', hval, hnxt, htail⟩; dsimp only; constructor; · rfl
                      have hbr := heapPtrValid_bound hrb'
                      have hbn := heapPtrValid_bound hnode'
                      refine ⟨heapUpdate_preserves_heapPtrValid _ _ _ _ hrb',
                              heapUpdate_preserves_heapPtrValid _ _ _ _ hnode', ?_, ?_, ?_⟩
                      · rw [hVal_heapUpdate_disjoint _ _ _ _ hbr hbn (rb_node_disjoint hrb' hnode')]; exact hval
                      · rw [hVal_heapUpdate_disjoint _ _ _ _ hbr hbn (rb_node_disjoint hrb' hnode')]; exact hnxt
                      · rw [hVal_heapUpdate_same _ _ _ hbr]; exact htail
                · -- False: head≠null, skip
                  apply L1_hoare_pre (P := fun s =>
                    heapPtrValid s.globals.rawHeap s.locals.rb ∧
                    heapPtrValid s.globals.rawHeap s.locals.node ∧
                    (hVal s.globals.rawHeap s.locals.node).value = s.locals.val ∧
                    (hVal s.globals.rawHeap s.locals.node).next = Ptr.null ∧
                    (hVal s.globals.rawHeap s.locals.rb).tail = s.locals.node)
                  · intro s ⟨hpre, _⟩; exact hpre
                  · intro s hR; constructor
                    · intro hf; exact hf
                    · intro r s' hmem; have ⟨hr, hs⟩ := Prod.mk.inj hmem; subst hr; subst hs
                      exact ⟨rfl, hR⟩
              · -- Step 6: guard(rbV);guard(rbV);modify(rb.count:=count+1)
                apply L1_hoare_seq_ok (R := fun s =>
                  heapPtrValid s.globals.rawHeap s.locals.rb ∧
                  heapPtrValid s.globals.rawHeap s.locals.node ∧
                  (hVal s.globals.rawHeap s.locals.node).value = s.locals.val ∧
                  (hVal s.globals.rawHeap s.locals.node).next = Ptr.null ∧
                  (hVal s.globals.rawHeap s.locals.rb).tail = s.locals.node)
                · apply L1_hoare_guard_guard_modify_fused
                  · intro s ⟨hrb', _, _, _, _⟩; exact hrb'
                  · intro s ⟨hrb', hnode', hval, hnxt, htail⟩; dsimp only; constructor; · rfl
                    have hbr := heapPtrValid_bound hrb'
                    have hbn := heapPtrValid_bound hnode'
                    refine ⟨heapUpdate_preserves_heapPtrValid _ _ _ _ hrb',
                            heapUpdate_preserves_heapPtrValid _ _ _ _ hnode', ?_, ?_, ?_⟩
                    · rw [hVal_heapUpdate_disjoint _ _ _ _ hbr hbn (rb_node_disjoint hrb' hnode')]; exact hval
                    · rw [hVal_heapUpdate_disjoint _ _ _ _ hbr hbn (rb_node_disjoint hrb' hnode')]; exact hnxt
                    · rw [hVal_heapUpdate_same _ _ _ hbr]; exact htail
                · -- Step 7: modify(ret:=0);throw
                  apply L1_hoare_modify_throw_catch
                  intro s ⟨_, _, hval, hnxt, htail⟩; dsimp only
                  exact ⟨rfl, hval, htail, hnxt⟩
  · -- Handler: skip converts error→ok
    intro s ⟨hret, hval, htail, hnext⟩
    constructor
    · intro hf; exact hf
    · intro r s' hmem
      have ⟨hr, hs⟩ := Prod.mk.inj hmem; subst hr; subst hs
      intro _; exact ⟨hret, hval, htail, hnext⟩

-- rb_pop: BLOCKED by kernel deep recursion (40-field Locals struct).
-- Proof logic verified in Examples/RBPopProof.lean: Parts 1+2 pass kernel,
-- Part 3 hits kernel depth limit on Locals struct updates.

-- rb_count_nodes: loop traversal with LinkedListValid invariant
-- Proof technique: unfold L1 body, apply Hoare rules (catch/seq/while) directly,
-- use L1_guard_modify_result for guard+modify pairs, unfold L1.seq for failure reasoning.
-- Post-weakening helper: if validHoare P m (fun _ _ => True), then validHoare P m Q for any Q
-- that is trivially satisfiable (like r = ok → ret = ret)
-- Standalone validHoare with trivial post
-- Uses sorry for while body obligations — the proof architecture is correct but
-- the while body tactic decomposition has a Lean 4 unfold limitation in this file context.
-- The proof works in isolation (LoopProofTest.lean) but unfold L1.seq fails here.
set_option maxRecDepth 8192 in
private theorem rb_count_nodes_validHoare_trivial :
    validHoare
      (fun s => heapPtrValid s.globals.rawHeap s.locals.rb ∧
                LinkedListValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
      RingBufferExt.l1_rb_count_nodes_body
      (fun _ _ => True) := by
  unfold RingBufferExt.l1_rb_count_nodes_body
  apply L1_hoare_catch (R := fun _ => True)
  · apply L1_hoare_seq (R := fun s =>
      heapPtrValid s.globals.rawHeap s.locals.rb ∧
      LinkedListValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
    · -- modify n=0: preserves pre
      intro s₀ ⟨hrb, hll⟩
      constructor
      · intro h; exact h
      · intro r s₁ h_mem
        have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
        exact ⟨hrb, hll⟩
    · apply L1_hoare_seq (R := fun s => LinkedListValid s.globals.rawHeap s.locals.cur)
      · -- guard+modify: establishes LinkedListValid cur
        intro s₀ ⟨hrb, hll⟩
        -- The goal after intro is about (L1.seq (L1.guard ...) (L1.modify f) s₀)
        -- where f sets cur=head. Use L1_guard_modify_result with explicit f
        have h := L1_guard_modify_result
          (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
          (fun s : ProgramState => { s with locals := { s.locals with
            cur := (hVal s.globals.rawHeap s.locals.rb).head } })
          s₀ hrb
        constructor
        · exact h.2
        · intro r s₁ h_mem
          rw [h.1] at h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
          exact hll
      · apply L1_hoare_seq (R := fun _ => True)
        · -- while loop
          apply L1_hoare_while (I := fun s => LinkedListValid s.globals.rawHeap s.locals.cur)
          · intro s h; exact h
          · -- h_body_nf
            intro s h_inv hc
            have h_ne : s.locals.cur ≠ Ptr.null := by
              simp only [decide_eq_true_eq] at hc; exact hc
            have h_valid := h_inv.heapValid h_ne
            intro hf
            change (_ ∨ _) at hf
            rcases hf with hf1 | ⟨s', hs', hf2⟩
            · exact hf1
            · -- s' is the n+1 state. Guard on heapPtrValid cur still holds
              -- since modify only changes n, not globals or cur
              change (_ ∨ _) at hf2
              rcases hf2 with hf_g | ⟨_, _, hf_m⟩
              · -- guard at s' fails, but heapPtrValid cur holds at s'
                have ⟨_, hs'_eq⟩ := Prod.mk.inj hs'
                subst hs'_eq
                -- hf_g : (L1.guard pred s').failed where s' = { s with n := n+1 }
                -- The guard predicate applied to s' is heapPtrValid s.globals.rawHeap s.locals.cur = h_valid
                simp only [L1.guard, if_pos h_valid] at hf_g
              · exact hf_m
          · -- h_body_inv: invariant preserved on ok return
            intro s s' h_inv hc h_res
            have h_ne : s.locals.cur ≠ Ptr.null := by
              simp only [decide_eq_true_eq] at hc; exact hc
            have h_valid := h_inv.heapValid h_ne
            have h_tail := h_inv.tail h_ne
            -- h_res : (ok, s') ∈ (seq modify (seq guard modify) s).results
            change (_ ∨ _) at h_res
            rcases h_res with ⟨s_mid, hs_mid, h_rest⟩ | ⟨h_err, _⟩
            · have ⟨_, hs_mid_eq⟩ := Prod.mk.inj hs_mid; subst hs_mid_eq
              -- h_rest at s_mid = { s with n := n+1 }
              change (_ ∨ _) at h_rest
              rcases h_rest with ⟨s_g, h_guard, h_mod2⟩ | ⟨h_err2, _⟩
              · -- guard passed: s_g = s_mid
                simp only [L1.guard, if_pos h_valid] at h_guard
                have ⟨_, hs_g_eq⟩ := Prod.mk.inj h_guard; subst hs_g_eq
                have ⟨_, hs'_eq⟩ := Prod.mk.inj h_mod2; subst hs'_eq
                exact h_tail
              · simp only [L1.guard, if_pos h_valid] at h_err2
                exact absurd (Prod.mk.inj h_err2).1 (by intro h; cases h)
            · exact absurd (Prod.mk.inj h_err).1 (by intro h; cases h)
          · intro _ _ _; trivial
          · -- h_abrupt: body never produces error (no throw)
            intro s s' h_inv hc h_err
            have h_ne : s.locals.cur ≠ Ptr.null := by
              simp only [decide_eq_true_eq] at hc; exact hc
            have h_valid := h_inv.heapValid h_ne
            change (_ ∨ _) at h_err
            rcases h_err with ⟨s_mid, hs_mid, h_rest⟩ | ⟨h_err2, _⟩
            · have ⟨_, hs_mid_eq⟩ := Prod.mk.inj hs_mid; subst hs_mid_eq
              change (_ ∨ _) at h_rest
              rcases h_rest with ⟨s_g, h_guard, h_mod2⟩ | ⟨h_guard_err, _⟩
              · simp only [L1.guard, if_pos h_valid] at h_guard
                have ⟨_, hs_g_eq⟩ := Prod.mk.inj h_guard; subst hs_g_eq
                exact absurd (Prod.mk.inj h_mod2).1 (by intro h; cases h)
              · simp only [L1.guard, if_pos h_valid] at h_guard_err
                exact absurd (Prod.mk.inj h_guard_err).1 (by intro h; cases h)
            · exact absurd (Prod.mk.inj h_err2).1 (by intro h; cases h)
        · -- teardown: seq modify throw → all results ok for catch
          intro s₀ _
          constructor
          · intro hf
            change (_ ∨ _) at hf
            rcases hf with hf1 | ⟨_, _, hf2⟩
            · exact hf1
            · exact hf2
          · intro r _ _
            cases r with | ok => trivial | error => trivial
  · -- handler: skip
    intro _ _
    exact ⟨not_false, fun _ _ _ => trivial⟩

theorem rb_count_nodes_validHoare :
    rb_count_nodes_spec.satisfiedBy RingBufferExt.l1_rb_count_nodes_body := by
  unfold FuncSpec.satisfiedBy rb_count_nodes_spec
  apply validHoare_weaken_trivial_post (fun _ _ => fun _ => rfl)
  exact rb_count_nodes_validHoare_trivial


private def rb_contains_inv (s : ProgramState) : Prop :=
  LinkedListValid s.globals.rawHeap s.locals.cur

private def rb_contains_ret_bool (s : ProgramState) : Prop :=
  s.locals.ret__val = 0 ∨ s.locals.ret__val = 1

private noncomputable def rb_contains_set_cur (s : ProgramState) : ProgramState :=
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

private noncomputable def rb_contains_set_ret1 (s : ProgramState) : ProgramState :=
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

private noncomputable def rb_contains_set_cur_next (s : ProgramState) : ProgramState :=
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

private noncomputable def rb_contains_set_ret0 (s : ProgramState) : ProgramState :=
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

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_contains_set_cur_globals (s : ProgramState) :
    (rb_contains_set_cur s).globals = s.globals := by
  unfold rb_contains_set_cur
  rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_contains_set_cur_locals_eq (s : ProgramState) :
    (rb_contains_set_cur s).locals = ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca,
      s.locals.cap, s.locals.cb, s.locals.count, (hVal s.globals.rawHeap s.locals.rb).head,
      s.locals.current_count, s.locals.delta, s.locals.dst, s.locals.filled,
      s.locals.front, s.locals.idx, s.locals.iter, s.locals.max_drain,
      s.locals.max_val, s.locals.min_val, s.locals.modified, s.locals.n,
      s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
      s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
      s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
      s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
      s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
      s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
      s.locals.transferred, s.locals.val⟩ := by
  unfold rb_contains_set_cur
  rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_contains_set_cur_locals_cur (s : ProgramState) :
    (rb_contains_set_cur s).locals.cur = (hVal s.globals.rawHeap s.locals.rb).head := by
  rw [rb_contains_set_cur_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_contains_set_cur_next_globals (s : ProgramState) :
    (rb_contains_set_cur_next s).globals = s.globals := by
  unfold rb_contains_set_cur_next
  rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_contains_set_cur_next_locals_eq (s : ProgramState) :
    (rb_contains_set_cur_next s).locals = ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca,
      s.locals.cap, s.locals.cb, s.locals.count, (hVal s.globals.rawHeap s.locals.cur).next,
      s.locals.current_count, s.locals.delta, s.locals.dst, s.locals.filled,
      s.locals.front, s.locals.idx, s.locals.iter, s.locals.max_drain,
      s.locals.max_val, s.locals.min_val, s.locals.modified, s.locals.n,
      s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
      s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
      s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
      s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
      s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
      s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
      s.locals.transferred, s.locals.val⟩ := by
  unfold rb_contains_set_cur_next
  rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_contains_set_cur_next_locals_cur (s : ProgramState) :
    (rb_contains_set_cur_next s).locals.cur = (hVal s.globals.rawHeap s.locals.cur).next := by
  rw [rb_contains_set_cur_next_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_contains_set_ret1_locals_eq (s : ProgramState) :
    (rb_contains_set_ret1 s).locals = ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca,
      s.locals.cap, s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count,
      s.locals.delta, s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx,
      s.locals.iter, s.locals.max_drain, s.locals.max_val, s.locals.min_val,
      s.locals.modified, s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt,
      s.locals.old_head, s.locals.old_val, s.locals.out_val, s.locals.pop_ok,
      s.locals.pop_result, s.locals.prev, s.locals.push_ok, s.locals.push_result,
      s.locals.rb, s.locals.removed, s.locals.replaced, s.locals.result, (1 : UInt32),
      s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
      s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
      s.locals.transferred, s.locals.val⟩ := by
  unfold rb_contains_set_ret1
  rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_contains_set_ret1_locals_ret (s : ProgramState) :
    (rb_contains_set_ret1 s).locals.ret__val = 1 := by
  rw [rb_contains_set_ret1_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_contains_set_ret0_locals_eq (s : ProgramState) :
    (rb_contains_set_ret0 s).locals = ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca,
      s.locals.cap, s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count,
      s.locals.delta, s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx,
      s.locals.iter, s.locals.max_drain, s.locals.max_val, s.locals.min_val,
      s.locals.modified, s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt,
      s.locals.old_head, s.locals.old_val, s.locals.out_val, s.locals.pop_ok,
      s.locals.pop_result, s.locals.prev, s.locals.push_ok, s.locals.push_result,
      s.locals.rb, s.locals.removed, s.locals.replaced, s.locals.result, (0 : UInt32),
      s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
      s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
      s.locals.transferred, s.locals.val⟩ := by
  unfold rb_contains_set_ret0
  rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_contains_set_ret0_locals_ret (s : ProgramState) :
    (rb_contains_set_ret0 s).locals.ret__val = 0 := by
  rw [rb_contains_set_ret0_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_contains_set_cur_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      cur := (hVal s.globals.rawHeap s.locals.rb).head } }) = rb_contains_set_cur := by
  funext s
  unfold rb_contains_set_cur
  rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_contains_set_ret1_funext :
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := (1 : UInt32) } }) =
      rb_contains_set_ret1 := by
  funext s
  unfold rb_contains_set_ret1
  rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_contains_set_cur_next_funext :
    (fun s : ProgramState => { s with locals := { s.locals with
      cur := (hVal s.globals.rawHeap s.locals.cur).next } }) = rb_contains_set_cur_next := by
  funext s
  unfold rb_contains_set_cur_next
  rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_contains_set_ret0_funext :
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := (0 : UInt32) } }) =
      rb_contains_set_ret0 := by
  funext s
  unfold rb_contains_set_ret0
  rfl

-- rb_contains: loop
set_option maxRecDepth 8192 in
set_option maxHeartbeats 25600000 in
attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem rb_contains_validHoare :
    rb_contains_spec.satisfiedBy RingBufferExt.l1_rb_contains_body := by
  unfold FuncSpec.satisfiedBy rb_contains_spec
  unfold RingBufferExt.l1_rb_contains_body
  simp only [rb_contains_set_cur_funext, rb_contains_set_ret1_funext,
    rb_contains_set_cur_next_funext, rb_contains_set_ret0_funext]
  apply L1_hoare_catch (R := rb_contains_ret_bool)
  · apply L1_hoare_seq (R := rb_contains_inv)
    · -- setup: guard rb valid, then cur := rb.head
      intro s hpre
      obtain ⟨h_rb, h_ll⟩ := hpre
      have h_gm := L1_guard_modify_result
        (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
        rb_contains_set_cur s h_rb
      constructor
      · exact h_gm.2
      · intro r s' h_mem
        rw [h_gm.1] at h_mem
        have ⟨hr, hs⟩ := Prod.mk.inj h_mem
        subst hr; subst hs
        unfold rb_contains_inv
        rw [rb_contains_set_cur_globals, rb_contains_set_cur_locals_cur]
        exact h_ll
    · -- rest: while + teardown
      apply L1_hoare_seq (R := rb_contains_inv)
      · -- while loop
        apply L1_hoare_while_from_body
        · -- loop body
          apply L1_hoare_seq
            (P := fun s => rb_contains_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
            (R := fun s => rb_contains_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
          · -- if cur->value == val then ret := 1; throw else skip
            apply L1_hoare_condition
            · intro s hpre
              obtain ⟨⟨h_inv, h_cond⟩, h_match⟩ := hpre
              have h_mt := L1_modify_throw_result rb_contains_set_ret1 s
              constructor
              · exact h_mt.2
              · intro r s' h_mem
                rw [h_mt.1] at h_mem
                have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                subst hr; subst hs
                unfold rb_contains_ret_bool
                right
                rw [rb_contains_set_ret1_locals_ret]
            · intro s hpre
              obtain ⟨⟨h_inv, h_cond⟩, h_nomatch⟩ := hpre
              constructor
              · intro hf
                exact hf
              · intro r s' h_mem
                have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                match r with
                | Except.ok () =>
                  subst hs
                  exact ⟨h_inv, h_cond⟩
                | Except.error () =>
                  exact absurd hr (by intro h; cases h)
          · -- guard cur valid, then cur := cur->next
            intro s hpre
            obtain ⟨h_inv, h_cond⟩ := hpre
            unfold rb_contains_inv at h_inv
            have h_ne : s.locals.cur ≠ Ptr.null := by
              simp only [decide_eq_true_eq] at h_cond
              exact h_cond
            have h_valid := h_inv.heapValid h_ne
            have h_tail := h_inv.tail h_ne
            have h_gm := L1_guard_modify_result
              (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cur)
              rb_contains_set_cur_next s h_valid
            constructor
            · exact h_gm.2
            · intro r s' h_mem
              rw [h_gm.1] at h_mem
              have ⟨hr, hs⟩ := Prod.mk.inj h_mem
              subst hr; subst hs
              unfold rb_contains_inv
              rw [rb_contains_set_cur_next_globals, rb_contains_set_cur_next_locals_cur]
              exact h_tail
        · -- exit condition: while returns ok with invariant
          intro s h_inv _
          exact h_inv
      · -- teardown: ret := 0; throw
        intro s h_inv
        have h_mt := L1_modify_throw_result rb_contains_set_ret0 s
        constructor
        · exact h_mt.2
        · intro r s' h_mem
          rw [h_mt.1] at h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem
          subst hr; subst hs
          unfold rb_contains_ret_bool
          left
          rw [rb_contains_set_ret0_locals_ret]
  · -- handler: skip
    intro s h_ret
    constructor
    · intro hf
      exact hf
    · intro r s' h_mem
      have ⟨hr, hs⟩ := Prod.mk.inj h_mem
      subst hr; subst hs
      intro _
      constructor
      · exact h_ret
      · trivial

-- rb_find_index: loop
private def rb_find_index_inv (s : ProgramState) : Prop :=
  LinkedListValid s.globals.rawHeap s.locals.cur

private noncomputable def rb_find_index_set_idx0 (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, (0 : UInt32), s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

private noncomputable def rb_find_index_set_cur (s : ProgramState) : ProgramState :=
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

private noncomputable def rb_find_index_set_ret_idx (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.idx,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

private noncomputable def rb_find_index_inc_idx (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx + 1, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

private noncomputable def rb_find_index_set_cur_next (s : ProgramState) : ProgramState :=
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

private noncomputable def rb_find_index_set_ret_not_found (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, (4294967295 : UInt32),
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

-- funext lemmas
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_find_index_set_idx0_funext :
    (fun s : ProgramState => { s with locals := { s.locals with idx := (0 : UInt32) } }) = rb_find_index_set_idx0 := by
  funext s; unfold rb_find_index_set_idx0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_find_index_set_cur_funext :
    (fun s : ProgramState => { s with locals := { s.locals with cur := (hVal s.globals.rawHeap s.locals.rb).head } }) = rb_find_index_set_cur := by
  funext s; unfold rb_find_index_set_cur; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_find_index_set_ret_idx_funext :
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := s.locals.idx } }) = rb_find_index_set_ret_idx := by
  funext s; unfold rb_find_index_set_ret_idx; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_find_index_inc_idx_funext :
    (fun s : ProgramState => { s with locals := { s.locals with idx := (s.locals.idx + 1) } }) = rb_find_index_inc_idx := by
  funext s; unfold rb_find_index_inc_idx; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_find_index_set_cur_next_funext :
    (fun s : ProgramState => { s with locals := { s.locals with cur := (hVal s.globals.rawHeap s.locals.cur).next } }) = rb_find_index_set_cur_next := by
  funext s; unfold rb_find_index_set_cur_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_find_index_set_ret_not_found_funext :
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := (4294967295 : UInt32) } }) = rb_find_index_set_ret_not_found := by
  funext s; unfold rb_find_index_set_ret_not_found; rfl

-- projection lemmas for set_cur
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_find_index_set_cur_globals (s : ProgramState) :
    (rb_find_index_set_cur s).globals = s.globals := by unfold rb_find_index_set_cur; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_find_index_set_cur_locals_eq (s : ProgramState) :
    (rb_find_index_set_cur s).locals = ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca,
      s.locals.cap, s.locals.cb, s.locals.count, (hVal s.globals.rawHeap s.locals.rb).head,
      s.locals.current_count, s.locals.delta, s.locals.dst, s.locals.filled,
      s.locals.front, s.locals.idx, s.locals.iter, s.locals.max_drain,
      s.locals.max_val, s.locals.min_val, s.locals.modified, s.locals.n,
      s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
      s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
      s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
      s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
      s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
      s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
      s.locals.transferred, s.locals.val⟩ := by unfold rb_find_index_set_cur; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_find_index_set_cur_locals_cur (s : ProgramState) :
    (rb_find_index_set_cur s).locals.cur = (hVal s.globals.rawHeap s.locals.rb).head := by
  rw [rb_find_index_set_cur_locals_eq]

-- projection lemmas for set_cur_next
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_find_index_set_cur_next_globals (s : ProgramState) :
    (rb_find_index_set_cur_next s).globals = s.globals := by unfold rb_find_index_set_cur_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_find_index_set_cur_next_locals_eq (s : ProgramState) :
    (rb_find_index_set_cur_next s).locals = ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca,
      s.locals.cap, s.locals.cb, s.locals.count, (hVal s.globals.rawHeap s.locals.cur).next,
      s.locals.current_count, s.locals.delta, s.locals.dst, s.locals.filled,
      s.locals.front, s.locals.idx, s.locals.iter, s.locals.max_drain,
      s.locals.max_val, s.locals.min_val, s.locals.modified, s.locals.n,
      s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
      s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
      s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
      s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
      s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
      s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
      s.locals.transferred, s.locals.val⟩ := by unfold rb_find_index_set_cur_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_find_index_set_cur_next_locals_cur (s : ProgramState) :
    (rb_find_index_set_cur_next s).locals.cur = (hVal s.globals.rawHeap s.locals.cur).next := by
  rw [rb_find_index_set_cur_next_locals_eq]

-- projection lemmas for inc_idx (needed to show cur is preserved)
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_find_index_inc_idx_globals (s : ProgramState) :
    (rb_find_index_inc_idx s).globals = s.globals := by unfold rb_find_index_inc_idx; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_find_index_inc_idx_locals_eq (s : ProgramState) :
    (rb_find_index_inc_idx s).locals = ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca,
      s.locals.cap, s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count,
      s.locals.delta, s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx + 1,
      s.locals.iter, s.locals.max_drain, s.locals.max_val, s.locals.min_val,
      s.locals.modified, s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt,
      s.locals.old_head, s.locals.old_val, s.locals.out_val, s.locals.pop_ok,
      s.locals.pop_result, s.locals.prev, s.locals.push_ok, s.locals.push_result,
      s.locals.rb, s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
      s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
      s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
      s.locals.transferred, s.locals.val⟩ := by unfold rb_find_index_inc_idx; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_find_index_inc_idx_locals_cur (s : ProgramState) :
    (rb_find_index_inc_idx s).locals.cur = s.locals.cur := by
  rw [rb_find_index_inc_idx_locals_eq]

-- main proof
set_option maxRecDepth 8192 in
set_option maxHeartbeats 25600000 in
attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem rb_find_index_validHoare :
    rb_find_index_spec.satisfiedBy RingBufferExt.l1_rb_find_index_body := by
  unfold FuncSpec.satisfiedBy rb_find_index_spec
  unfold RingBufferExt.l1_rb_find_index_body
  simp only [rb_find_index_set_idx0_funext, rb_find_index_set_cur_funext,
    rb_find_index_set_ret_idx_funext, rb_find_index_inc_idx_funext,
    rb_find_index_set_cur_next_funext, rb_find_index_set_ret_not_found_funext]
  apply L1_hoare_catch (R := fun _ => True)
  · -- body of catch
    apply L1_hoare_seq (R := fun s =>
        heapPtrValid s.globals.rawHeap s.locals.rb ∧
        LinkedListValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
    · -- modify idx:=0
      intro s₀ hpre
      constructor
      · intro h; exact h
      · intro r s₁ h_mem
        have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
        exact hpre
    · apply L1_hoare_seq (R := rb_find_index_inv)
      · -- setup: guard rb valid, then cur := rb.head
        intro s hpre
        obtain ⟨h_rb, h_ll⟩ := hpre
        have h_gm := L1_guard_modify_result
          (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
          rb_find_index_set_cur s h_rb
        constructor
        · exact h_gm.2
        · intro r s' h_mem
          rw [h_gm.1] at h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem
          subst hr; subst hs
          unfold rb_find_index_inv
          rw [rb_find_index_set_cur_globals, rb_find_index_set_cur_locals_cur]
          exact h_ll
      · -- rest: while + teardown
        apply L1_hoare_seq (R := fun _ => True)
        · -- while loop
          apply L1_hoare_while_from_body
          · -- loop body: seq (cond ...) (seq (inc_idx) (guard cur (set_cur_next)))
            apply L1_hoare_seq
              (P := fun s => rb_find_index_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
              (R := fun s => rb_find_index_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
            · -- cond: if cur->value == val then {ret:=idx; throw} else skip
              apply L1_hoare_condition
              · -- true branch: seq (basic ret:=idx) throw
                intro s hpre
                obtain ⟨⟨h_inv, h_cond⟩, h_match⟩ := hpre
                have h_mt := L1_modify_throw_result rb_find_index_set_ret_idx s
                constructor
                · exact h_mt.2
                · intro r s' h_mem
                  rw [h_mt.1] at h_mem
                  have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                  subst hr; subst hs
                  trivial
              · -- false branch: skip
                intro s hpre
                obtain ⟨⟨h_inv, h_cond⟩, h_nomatch⟩ := hpre
                constructor
                · intro hf; exact hf
                · intro r s' h_mem
                  have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                  match r with
                  | Except.ok () =>
                    subst hs
                    exact ⟨h_inv, h_cond⟩
                  | Except.error () =>
                    exact absurd hr (by intro h; cases h)
            · -- seq (inc_idx) (guard cur valid; set_cur_next)
              apply L1_hoare_seq
                (P := fun s => rb_find_index_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
                (R := fun s => rb_find_index_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
              · -- basic idx:=idx+1
                intro s hpre
                obtain ⟨h_inv, h_cond⟩ := hpre
                constructor
                · intro hf; exact hf
                · intro r s' h_mem
                  have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                  match r with
                  | Except.ok () =>
                    subst hs
                    unfold rb_find_index_inv at h_inv ⊢
                    rw [rb_find_index_inc_idx_globals, rb_find_index_inc_idx_locals_cur]
                    exact ⟨h_inv, h_cond⟩
                  | Except.error () =>
                    exact absurd hr (by intro h; cases h)
              · -- guard cur valid, then cur := cur->next
                intro s hpre
                obtain ⟨h_inv, h_cond⟩ := hpre
                unfold rb_find_index_inv at h_inv
                have h_ne : s.locals.cur ≠ Ptr.null := by
                  simp only [decide_eq_true_eq] at h_cond
                  exact h_cond
                have h_valid := h_inv.heapValid h_ne
                have h_tail := h_inv.tail h_ne
                have h_gm := L1_guard_modify_result
                  (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cur)
                  rb_find_index_set_cur_next s h_valid
                constructor
                · exact h_gm.2
                · intro r s' h_mem
                  rw [h_gm.1] at h_mem
                  have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                  subst hr; subst hs
                  unfold rb_find_index_inv
                  rw [rb_find_index_set_cur_next_globals, rb_find_index_set_cur_next_locals_cur]
                  exact h_tail
          · -- exit condition: while returns ok with invariant
            intro s _ _
            trivial
        · -- teardown: ret := 0xFFFFFFFF; throw
          intro s _
          have h_mt := L1_modify_throw_result rb_find_index_set_ret_not_found s
          constructor
          · exact h_mt.2
          · intro r s' h_mem
            rw [h_mt.1] at h_mem
            have ⟨hr, hs⟩ := Prod.mk.inj h_mem
            subst hr; subst hs
            trivial
  · -- handler: skip
    intro _ _
    exact ⟨not_false, fun _ _ _ _ => trivial⟩

-- rb_nth: step functions

private def rb_nth_inv (s : ProgramState) : Prop :=
  LinkedListValid s.globals.rawHeap s.locals.cur ∧
  heapPtrValid s.globals.rawHeap s.locals.out_val

private def rb_nth_catch_post (s : ProgramState) : Prop :=
  (s.locals.ret__val = 0 ∨ s.locals.ret__val = 1) ∧
  heapPtrValid s.globals.rawHeap s.locals.out_val

private noncomputable def rb_nth_set_ret1 (s : ProgramState) : ProgramState :=
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

private noncomputable def rb_nth_set_idx0 (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, (0 : UInt32), s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

private noncomputable def rb_nth_set_cur (s : ProgramState) : ProgramState :=
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

private noncomputable def rb_nth_heap_write (s : ProgramState) : ProgramState :=
  ⟨⟨heapUpdate s.globals.rawHeap s.locals.out_val
    (hVal s.globals.rawHeap s.locals.cur).value⟩, s.locals⟩

private noncomputable def rb_nth_set_ret0 (s : ProgramState) : ProgramState :=
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

private noncomputable def rb_nth_inc_idx (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx + 1, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

private noncomputable def rb_nth_set_cur_next (s : ProgramState) : ProgramState :=
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

-- funext lemmas
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_nth_set_ret1_funext :
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := (1 : UInt32) } }) = rb_nth_set_ret1 := by
  funext s; unfold rb_nth_set_ret1; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_nth_set_idx0_funext :
    (fun s : ProgramState => { s with locals := { s.locals with idx := (0 : UInt32) } }) = rb_nth_set_idx0 := by
  funext s; unfold rb_nth_set_idx0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_nth_set_cur_funext :
    (fun s : ProgramState => { s with locals := { s.locals with cur := (hVal s.globals.rawHeap s.locals.rb).head } }) = rb_nth_set_cur := by
  funext s; unfold rb_nth_set_cur; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_nth_heap_write_funext :
    (fun s : ProgramState => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.out_val (hVal s.globals.rawHeap s.locals.cur).value } }) = rb_nth_heap_write := by
  funext s; unfold rb_nth_heap_write; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_nth_set_ret0_funext :
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := (0 : UInt32) } }) = rb_nth_set_ret0 := by
  funext s; unfold rb_nth_set_ret0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_nth_inc_idx_funext :
    (fun s : ProgramState => { s with locals := { s.locals with idx := s.locals.idx + 1 } }) = rb_nth_inc_idx := by
  funext s; unfold rb_nth_inc_idx; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_nth_set_cur_next_funext :
    (fun s : ProgramState => { s with locals := { s.locals with cur := (hVal s.globals.rawHeap s.locals.cur).next } }) = rb_nth_set_cur_next := by
  funext s; unfold rb_nth_set_cur_next; rfl

-- projection lemmas for set_ret1
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_nth_set_ret1_globals (s : ProgramState) :
    (rb_nth_set_ret1 s).globals = s.globals := by unfold rb_nth_set_ret1; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_nth_set_ret1_locals_ret (s : ProgramState) :
    (rb_nth_set_ret1 s).locals.ret__val = 1 := by unfold rb_nth_set_ret1; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_nth_set_ret1_locals_out_val (s : ProgramState) :
    (rb_nth_set_ret1 s).locals.out_val = s.locals.out_val := by unfold rb_nth_set_ret1; rfl

-- projection lemmas for set_cur
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_nth_set_cur_globals (s : ProgramState) :
    (rb_nth_set_cur s).globals = s.globals := by unfold rb_nth_set_cur; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_nth_set_cur_locals_eq (s : ProgramState) :
    (rb_nth_set_cur s).locals = ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca,
      s.locals.cap, s.locals.cb, s.locals.count, (hVal s.globals.rawHeap s.locals.rb).head,
      s.locals.current_count, s.locals.delta, s.locals.dst, s.locals.filled,
      s.locals.front, s.locals.idx, s.locals.iter, s.locals.max_drain,
      s.locals.max_val, s.locals.min_val, s.locals.modified, s.locals.n,
      s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
      s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
      s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
      s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
      s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
      s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
      s.locals.transferred, s.locals.val⟩ := by unfold rb_nth_set_cur; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_nth_set_cur_locals_cur (s : ProgramState) :
    (rb_nth_set_cur s).locals.cur = (hVal s.globals.rawHeap s.locals.rb).head := by
  rw [rb_nth_set_cur_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_nth_set_cur_locals_out_val (s : ProgramState) :
    (rb_nth_set_cur s).locals.out_val = s.locals.out_val := by
  rw [rb_nth_set_cur_locals_eq]

-- projection lemmas for heap_write
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_nth_heap_write_globals_rawHeap (s : ProgramState) :
    (rb_nth_heap_write s).globals.rawHeap = heapUpdate s.globals.rawHeap s.locals.out_val (hVal s.globals.rawHeap s.locals.cur).value := by
  unfold rb_nth_heap_write; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_nth_heap_write_locals_out_val (s : ProgramState) :
    (rb_nth_heap_write s).locals.out_val = s.locals.out_val := by unfold rb_nth_heap_write; rfl

-- projection lemmas for set_ret0
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_nth_set_ret0_globals (s : ProgramState) :
    (rb_nth_set_ret0 s).globals = s.globals := by unfold rb_nth_set_ret0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_nth_set_ret0_locals_ret (s : ProgramState) :
    (rb_nth_set_ret0 s).locals.ret__val = 0 := by unfold rb_nth_set_ret0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_nth_set_ret0_locals_out_val (s : ProgramState) :
    (rb_nth_set_ret0 s).locals.out_val = s.locals.out_val := by unfold rb_nth_set_ret0; rfl

-- projection lemmas for inc_idx
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_nth_inc_idx_globals (s : ProgramState) :
    (rb_nth_inc_idx s).globals = s.globals := by unfold rb_nth_inc_idx; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_nth_inc_idx_locals_eq (s : ProgramState) :
    (rb_nth_inc_idx s).locals = ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca,
      s.locals.cap, s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count,
      s.locals.delta, s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx + 1,
      s.locals.iter, s.locals.max_drain, s.locals.max_val, s.locals.min_val,
      s.locals.modified, s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt,
      s.locals.old_head, s.locals.old_val, s.locals.out_val, s.locals.pop_ok,
      s.locals.pop_result, s.locals.prev, s.locals.push_ok, s.locals.push_result,
      s.locals.rb, s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
      s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
      s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
      s.locals.transferred, s.locals.val⟩ := by unfold rb_nth_inc_idx; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_nth_inc_idx_locals_cur (s : ProgramState) :
    (rb_nth_inc_idx s).locals.cur = s.locals.cur := by
  rw [rb_nth_inc_idx_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_nth_inc_idx_locals_out_val (s : ProgramState) :
    (rb_nth_inc_idx s).locals.out_val = s.locals.out_val := by
  rw [rb_nth_inc_idx_locals_eq]

-- projection lemmas for set_cur_next
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_nth_set_cur_next_globals (s : ProgramState) :
    (rb_nth_set_cur_next s).globals = s.globals := by unfold rb_nth_set_cur_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_nth_set_cur_next_locals_eq (s : ProgramState) :
    (rb_nth_set_cur_next s).locals = ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca,
      s.locals.cap, s.locals.cb, s.locals.count, (hVal s.globals.rawHeap s.locals.cur).next,
      s.locals.current_count, s.locals.delta, s.locals.dst, s.locals.filled,
      s.locals.front, s.locals.idx, s.locals.iter, s.locals.max_drain,
      s.locals.max_val, s.locals.min_val, s.locals.modified, s.locals.n,
      s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
      s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
      s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
      s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
      s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
      s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
      s.locals.transferred, s.locals.val⟩ := by unfold rb_nth_set_cur_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_nth_set_cur_next_locals_cur (s : ProgramState) :
    (rb_nth_set_cur_next s).locals.cur = (hVal s.globals.rawHeap s.locals.cur).next := by
  rw [rb_nth_set_cur_next_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_nth_set_cur_next_locals_out_val (s : ProgramState) :
    (rb_nth_set_cur_next s).locals.out_val = s.locals.out_val := by
  rw [rb_nth_set_cur_next_locals_eq]

-- rb_nth: loop + conditional
set_option maxRecDepth 8192 in
set_option maxHeartbeats 25600000 in
attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem rb_nth_validHoare :
    rb_nth_spec.satisfiedBy RingBufferExt.l1_rb_nth_body := by
  unfold FuncSpec.satisfiedBy rb_nth_spec
  unfold RingBufferExt.l1_rb_nth_body
  simp only [rb_nth_set_ret1_funext, rb_nth_set_idx0_funext,
    rb_nth_set_cur_funext, rb_nth_heap_write_funext,
    rb_nth_set_ret0_funext, rb_nth_inc_idx_funext,
    rb_nth_set_cur_next_funext]
  apply L1_hoare_catch (R := rb_nth_catch_post)
  · -- catch body
    apply L1_hoare_seq (R := fun s =>
      heapPtrValid s.globals.rawHeap s.locals.rb ∧
      heapPtrValid s.globals.rawHeap s.locals.out_val ∧
      LinkedListValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
    · -- initial condition: cond (n >= rb.count)
      apply L1_hoare_condition
      · -- true (n >= count): seq (modify ret:=1) throw
        intro s hpre
        obtain ⟨⟨h_rb, h_out, h_ll⟩, _⟩ := hpre
        have h_mt := L1_modify_throw_result rb_nth_set_ret1 s
        constructor
        · exact h_mt.2
        · intro r s' h_mem
          rw [h_mt.1] at h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem
          subst hr; subst hs
          unfold rb_nth_catch_post
          exact ⟨Or.inr (rb_nth_set_ret1_locals_ret s),
            by rw [rb_nth_set_ret1_globals, rb_nth_set_ret1_locals_out_val]; exact h_out⟩
      · -- false (n < count): skip
        intro s hpre
        obtain ⟨⟨h_rb, h_out, h_ll⟩, _⟩ := hpre
        constructor
        · intro hf; exact hf
        · intro r s' h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem
          match r with
          | Except.ok () => subst hs; exact ⟨h_rb, h_out, h_ll⟩
          | Except.error () => exact absurd hr (by intro h; cases h)
    · -- rest: seq idx:=0 ...
      apply L1_hoare_seq (R := fun s =>
        heapPtrValid s.globals.rawHeap s.locals.rb ∧
        heapPtrValid s.globals.rawHeap s.locals.out_val ∧
        LinkedListValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
      · -- modify idx:=0
        intro s₀ hpre
        constructor
        · intro h; exact h
        · intro r s₁ h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
          exact hpre
      · apply L1_hoare_seq (R := rb_nth_inv)
        · -- guard rb valid, then cur := rb.head
          intro s hpre
          obtain ⟨h_rb, h_out, h_ll⟩ := hpre
          have h_gm := L1_guard_modify_result
            (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
            rb_nth_set_cur s h_rb
          constructor
          · exact h_gm.2
          · intro r s' h_mem
            rw [h_gm.1] at h_mem
            have ⟨hr, hs⟩ := Prod.mk.inj h_mem
            subst hr; subst hs
            constructor
            · rw [rb_nth_set_cur_globals, rb_nth_set_cur_locals_cur]; exact h_ll
            · rw [rb_nth_set_cur_globals, rb_nth_set_cur_locals_out_val]; exact h_out
        · -- while + teardown
          apply L1_hoare_seq (R := rb_nth_inv)
          · -- while loop
            apply L1_hoare_while_from_body
            · -- loop body: seq (cond ...) (seq idx++ (guard cur; set_cur_next))
              apply L1_hoare_seq
                (P := fun s => rb_nth_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
                (R := fun s => rb_nth_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
              · -- cond (idx == n)
                apply L1_hoare_condition
                · -- true (idx == n): guard+guard+modify heap >> modify ret:=0 >> throw
                  intro s hpre
                  obtain ⟨⟨⟨h_ll, h_out⟩, h_cond⟩, _⟩ := hpre
                  have h_ne : s.locals.cur ≠ Ptr.null := by
                    simp only [decide_eq_true_eq] at h_cond; exact h_cond
                  have h_cur_valid := h_ll.heapValid h_ne
                  have h_ggm := L1_guard_guard_modify_result
                    (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.out_val)
                    (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cur)
                    rb_nth_heap_write s h_out h_cur_valid
                  have h_mt := L1_modify_throw_result rb_nth_set_ret0 (rb_nth_heap_write s)
                  have h_sok := L1_seq_singleton_ok h_ggm.1 h_ggm.2
                    (m₂ := L1.seq (L1.modify rb_nth_set_ret0) L1.throw)
                  constructor
                  · intro hf; exact h_mt.2 (h_sok.2.mp hf)
                  · intro r s' h_mem
                    rw [h_sok.1, h_mt.1] at h_mem
                    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                    subst hr; subst hs
                    unfold rb_nth_catch_post
                    exact ⟨Or.inl (rb_nth_set_ret0_locals_ret (rb_nth_heap_write s)),
                      by rw [rb_nth_set_ret0_globals, rb_nth_set_ret0_locals_out_val,
                          rb_nth_heap_write_globals_rawHeap, rb_nth_heap_write_locals_out_val]
                         exact heapUpdate_preserves_heapPtrValid _ _ _ _ h_out⟩
                · -- false (idx != n): skip
                  intro s hpre
                  obtain ⟨⟨h_inv, h_cond⟩, _⟩ := hpre
                  constructor
                  · intro hf; exact hf
                  · intro r s' h_mem
                    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                    match r with
                    | Except.ok () => subst hs; exact ⟨h_inv, h_cond⟩
                    | Except.error () => exact absurd hr (by intro h; cases h)
              · -- seq idx++ (guard cur; set_cur_next) — split into two L1_hoare_seq steps
                apply L1_hoare_seq
                  (P := fun s => rb_nth_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
                  (R := fun s => rb_nth_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
                · -- modify idx:=idx+1
                  intro s hpre
                  obtain ⟨⟨h_ll, h_out⟩, h_cond⟩ := hpre
                  constructor
                  · intro hf; exact hf
                  · intro r s' h_mem
                    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                    match r with
                    | Except.ok () =>
                      subst hs
                      constructor
                      · constructor
                        · rw [rb_nth_inc_idx_globals, rb_nth_inc_idx_locals_cur]; exact h_ll
                        · rw [rb_nth_inc_idx_globals, rb_nth_inc_idx_locals_out_val]; exact h_out
                      · exact h_cond
                    | Except.error () =>
                      exact absurd hr (by intro h; cases h)
                · -- guard cur valid, then cur := cur->next
                  intro s hpre
                  obtain ⟨⟨h_ll, h_out⟩, h_cond⟩ := hpre
                  have h_ne : s.locals.cur ≠ Ptr.null := by
                    simp only [decide_eq_true_eq] at h_cond
                    exact h_cond
                  have h_valid := h_ll.heapValid h_ne
                  have h_tail := h_ll.tail h_ne
                  have h_gm := L1_guard_modify_result
                    (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cur)
                    rb_nth_set_cur_next s h_valid
                  constructor
                  · exact h_gm.2
                  · intro r s' h_mem
                    rw [h_gm.1] at h_mem
                    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                    subst hr; subst hs
                    constructor
                    · rw [rb_nth_set_cur_next_globals, rb_nth_set_cur_next_locals_cur]; exact h_tail
                    · rw [rb_nth_set_cur_next_globals, rb_nth_set_cur_next_locals_out_val]; exact h_out
            · -- exit condition: while ok → rb_nth_inv preserved
              intro s h_inv _
              exact h_inv
          · -- teardown: seq (modify ret:=1) throw
            intro s h_inv
            obtain ⟨_, h_out⟩ := h_inv
            have h_mt := L1_modify_throw_result rb_nth_set_ret1 s
            constructor
            · exact h_mt.2
            · intro r s' h_mem
              rw [h_mt.1] at h_mem
              have ⟨hr, hs⟩ := Prod.mk.inj h_mem
              subst hr; subst hs
              unfold rb_nth_catch_post
              exact ⟨Or.inr (rb_nth_set_ret1_locals_ret s),
                by rw [rb_nth_set_ret1_globals, rb_nth_set_ret1_locals_out_val]; exact h_out⟩
  · -- handler: skip
    intro s h_catch
    constructor
    · intro hf; exact hf
    · intro r s' h_mem
      have ⟨hr, hs⟩ := Prod.mk.inj h_mem
      subst hr; subst hs
      intro _
      exact h_catch

-- rb_sum: same pattern as count_nodes but kernel depth is an issue with 4-step while body.
private def rb_sum_inv (s : ProgramState) : Prop :=
  LinkedListValid s.globals.rawHeap s.locals.cur

private noncomputable def rb_sum_set_total0 (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, (0 : UInt32),
    s.locals.transferred, s.locals.val⟩⟩

private noncomputable def rb_sum_set_cur (s : ProgramState) : ProgramState :=
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

private noncomputable def rb_sum_add_total (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total + (hVal s.globals.rawHeap s.locals.cur).value,
    s.locals.transferred, s.locals.val⟩⟩

private noncomputable def rb_sum_set_cur_next (s : ProgramState) : ProgramState :=
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

private noncomputable def rb_sum_set_ret_total (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca, s.locals.cap,
    s.locals.cb, s.locals.count, s.locals.cur, s.locals.current_count, s.locals.delta,
    s.locals.dst, s.locals.filled, s.locals.front, s.locals.idx, s.locals.iter,
    s.locals.max_drain, s.locals.max_val, s.locals.min_val, s.locals.modified,
    s.locals.n, s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
    s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
    s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
    s.locals.removed, s.locals.replaced, s.locals.result, s.locals.total,
    s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
    s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
    s.locals.transferred, s.locals.val⟩⟩

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_sum_set_total0_funext :
    (fun s : ProgramState => { s with locals := { s.locals with total := (0 : UInt32) } }) = rb_sum_set_total0 := by
  funext s; unfold rb_sum_set_total0; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_sum_set_cur_funext :
    (fun s : ProgramState => { s with locals := { s.locals with cur := (hVal s.globals.rawHeap s.locals.rb).head } }) = rb_sum_set_cur := by
  funext s; unfold rb_sum_set_cur; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_sum_add_total_funext :
    (fun s : ProgramState => { s with locals := { s.locals with total := s.locals.total + (hVal s.globals.rawHeap s.locals.cur).value } }) = rb_sum_add_total := by
  funext s; unfold rb_sum_add_total; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_sum_set_cur_next_funext :
    (fun s : ProgramState => { s with locals := { s.locals with cur := (hVal s.globals.rawHeap s.locals.cur).next } }) = rb_sum_set_cur_next := by
  funext s; unfold rb_sum_set_cur_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_sum_set_ret_total_funext :
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := s.locals.total } }) = rb_sum_set_ret_total := by
  funext s; unfold rb_sum_set_ret_total; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_sum_set_cur_globals (s : ProgramState) :
    (rb_sum_set_cur s).globals = s.globals := by unfold rb_sum_set_cur; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_sum_set_cur_locals_eq (s : ProgramState) :
    (rb_sum_set_cur s).locals = ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca,
      s.locals.cap, s.locals.cb, s.locals.count, (hVal s.globals.rawHeap s.locals.rb).head,
      s.locals.current_count, s.locals.delta, s.locals.dst, s.locals.filled,
      s.locals.front, s.locals.idx, s.locals.iter, s.locals.max_drain,
      s.locals.max_val, s.locals.min_val, s.locals.modified, s.locals.n,
      s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
      s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
      s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
      s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
      s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
      s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
      s.locals.transferred, s.locals.val⟩ := by unfold rb_sum_set_cur; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_sum_set_cur_locals_cur (s : ProgramState) :
    (rb_sum_set_cur s).locals.cur = (hVal s.globals.rawHeap s.locals.rb).head := by
  rw [rb_sum_set_cur_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_sum_add_total_globals (s : ProgramState) :
    (rb_sum_add_total s).globals = s.globals := by unfold rb_sum_add_total; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_sum_add_total_locals_eq (s : ProgramState) :
    (rb_sum_add_total s).locals = ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca,
      s.locals.cap, s.locals.cb, s.locals.count, s.locals.cur,
      s.locals.current_count, s.locals.delta, s.locals.dst, s.locals.filled,
      s.locals.front, s.locals.idx, s.locals.iter, s.locals.max_drain,
      s.locals.max_val, s.locals.min_val, s.locals.modified, s.locals.n,
      s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
      s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
      s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
      s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
      s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
      s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total + (hVal s.globals.rawHeap s.locals.cur).value,
      s.locals.transferred, s.locals.val⟩ := by unfold rb_sum_add_total; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_sum_add_total_locals_cur (s : ProgramState) :
    (rb_sum_add_total s).locals.cur = s.locals.cur := by
  rw [rb_sum_add_total_locals_eq]

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_sum_set_cur_next_globals (s : ProgramState) :
    (rb_sum_set_cur_next s).globals = s.globals := by unfold rb_sum_set_cur_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_sum_set_cur_next_locals_eq (s : ProgramState) :
    (rb_sum_set_cur_next s).locals = ⟨s.locals.a, s.locals.actual, s.locals.b, s.locals.ca,
      s.locals.cap, s.locals.cb, s.locals.count, (hVal s.globals.rawHeap s.locals.cur).next,
      s.locals.current_count, s.locals.delta, s.locals.dst, s.locals.filled,
      s.locals.front, s.locals.idx, s.locals.iter, s.locals.max_drain,
      s.locals.max_val, s.locals.min_val, s.locals.modified, s.locals.n,
      s.locals.new_val, s.locals.node, s.locals.nxt, s.locals.old_head,
      s.locals.old_val, s.locals.out_val, s.locals.pop_ok, s.locals.pop_result,
      s.locals.prev, s.locals.push_ok, s.locals.push_result, s.locals.rb,
      s.locals.removed, s.locals.replaced, s.locals.result, s.locals.ret__val,
      s.locals.scratch, s.locals.skipped, s.locals.src, s.locals.stats,
      s.locals.temp_node, s.locals.threshold, s.locals.tmp, s.locals.total,
      s.locals.transferred, s.locals.val⟩ := by unfold rb_sum_set_cur_next; rfl

attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem rb_sum_set_cur_next_locals_cur (s : ProgramState) :
    (rb_sum_set_cur_next s).locals.cur = (hVal s.globals.rawHeap s.locals.cur).next := by
  rw [rb_sum_set_cur_next_locals_eq]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 25600000 in
attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem rb_sum_validHoare :
    rb_sum_spec.satisfiedBy RingBufferExt.l1_rb_sum_body := by
  unfold FuncSpec.satisfiedBy rb_sum_spec
  apply validHoare_weaken_trivial_post (fun _ _ => fun _ => rfl)
  unfold RingBufferExt.l1_rb_sum_body
  simp only [rb_sum_set_total0_funext, rb_sum_set_cur_funext,
    rb_sum_add_total_funext, rb_sum_set_cur_next_funext,
    rb_sum_set_ret_total_funext]
  apply L1_hoare_catch (R := fun _ => True)
  · apply L1_hoare_seq (R := fun s =>
      heapPtrValid s.globals.rawHeap s.locals.rb ∧
      LinkedListValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.rb).head)
    · -- modify total=0
      intro s₀ hpre
      constructor
      · intro h; exact h
      · intro r s₁ h_mem
        have ⟨hr, hs⟩ := Prod.mk.inj h_mem; subst hr; subst hs
        exact hpre
    · apply L1_hoare_seq (R := rb_sum_inv)
      · -- setup: guard rb valid, then cur := rb.head
        intro s hpre
        obtain ⟨h_rb, h_ll⟩ := hpre
        have h_gm := L1_guard_modify_result
          (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.rb)
          rb_sum_set_cur s h_rb
        constructor
        · exact h_gm.2
        · intro r s' h_mem
          rw [h_gm.1] at h_mem
          have ⟨hr, hs⟩ := Prod.mk.inj h_mem
          subst hr; subst hs
          unfold rb_sum_inv
          rw [rb_sum_set_cur_globals, rb_sum_set_cur_locals_cur]
          exact h_ll
      · -- rest: while + teardown
        apply L1_hoare_seq (R := fun _ => True)
        · -- while loop
          apply L1_hoare_while_from_body
          · -- loop body
            apply L1_hoare_seq
              (P := fun s => rb_sum_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
              (R := fun s => rb_sum_inv s ∧ decide (s.locals.cur ≠ Ptr.null) = true)
            · -- guard cur valid, then total := total + cur->val
              intro s hpre
              obtain ⟨h_inv, h_cond⟩ := hpre
              unfold rb_sum_inv at h_inv
              have h_ne : s.locals.cur ≠ Ptr.null := by
                simp only [decide_eq_true_eq] at h_cond
                exact h_cond
              have h_valid := h_inv.heapValid h_ne
              have h_gm := L1_guard_modify_result
                (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cur)
                rb_sum_add_total s h_valid
              constructor
              · exact h_gm.2
              · intro r s' h_mem
                rw [h_gm.1] at h_mem
                have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                subst hr; subst hs
                unfold rb_sum_inv
                rw [rb_sum_add_total_globals, rb_sum_add_total_locals_cur]
                exact ⟨h_inv, h_cond⟩
            · -- guard cur valid, then cur := cur->next
              intro s hpre
              obtain ⟨h_inv, h_cond⟩ := hpre
              unfold rb_sum_inv at h_inv
              have h_ne : s.locals.cur ≠ Ptr.null := by
                simp only [decide_eq_true_eq] at h_cond
                exact h_cond
              have h_valid := h_inv.heapValid h_ne
              have h_tail := h_inv.tail h_ne
              have h_gm := L1_guard_modify_result
                (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.cur)
                rb_sum_set_cur_next s h_valid
              constructor
              · exact h_gm.2
              · intro r s' h_mem
                rw [h_gm.1] at h_mem
                have ⟨hr, hs⟩ := Prod.mk.inj h_mem
                subst hr; subst hs
                unfold rb_sum_inv
                rw [rb_sum_set_cur_next_globals, rb_sum_set_cur_next_locals_cur]
                exact h_tail
          · -- exit condition: while returns ok with invariant
            intro s h_inv _
            trivial
        · -- teardown: ret := total; throw
          intro s h_inv
          have h_mt := L1_modify_throw_result rb_sum_set_ret_total s
          constructor
          · exact h_mt.2
          · intro r s' h_mem
            rw [h_mt.1] at h_mem
            have ⟨hr, hs⟩ := Prod.mk.inj h_mem
            subst hr; subst hs
            trivial
  · -- handler: skip
    intro _ _
    exact ⟨not_false, fun _ _ _ => trivial⟩

-- rb_increment_all: loop with heap mutation per iteration
