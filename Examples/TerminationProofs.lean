-- Termination proofs for ring_buffer_ext functions (task 0170)
--
-- Demonstrates the pattern: prove Terminates for each function body,
-- then combine with cHoare to get cHoareTotal.
--
-- All functions proven here are loop-free (straight-line code), so
-- termination follows by structural decomposition: catch(seq(guard(basic);throw);skip)
-- all terminate because each sub-command terminates.
--
-- For functions WITH loops (rb_clear, rb_contains, etc.), termination
-- requires a decreasing measure (e.g., number of nodes remaining).
-- Those are deferred to a separate task.

import Generated.RingBufferExt
import Clift.CSemantics.TerminatesProps

set_option maxHeartbeats 3200000

open RingBufferExt

/-! # Helper: termination of common CSimpl patterns

The CImporter generates functions in a standard shape:
  catch (seq ... (seq (basic assign) throw)) skip

We build termination bottom-up from primitives. -/

section Helpers

variable {σ : Type} {Γ : ProcEnv σ} {s : σ}

-- Throw always terminates
private theorem term_throw :
    Terminates Γ (.throw : CSimpl σ) s :=
  Terminates.throw s

-- Skip always terminates
private theorem term_skip :
    Terminates Γ (.skip : CSimpl σ) s :=
  Terminates.skip s

-- Basic always terminates
private theorem term_basic {f : σ → σ} :
    Terminates Γ (.basic f) s :=
  Terminates.basic f s

-- seq(basic, throw) terminates
private theorem term_basic_throw {f : σ → σ} :
    Terminates Γ (.seq (.basic f) .throw) s := by
  apply Terminates.seq
  · exact Terminates.basic f s
  · intro t h_exec; cases h_exec; exact Terminates.throw _

-- guard(_, body) terminates if body terminates for every state
private theorem term_guard {pred : σ → Prop} {c : CSimpl σ}
    (h_body : Terminates Γ c s) :
    Terminates Γ (.guard pred c) s := by
  by_cases hp : pred s
  · exact Terminates.guardOk pred c s hp h_body
  · exact Terminates.guardFault pred c s hp

-- catch(body, skip) terminates if body terminates
private theorem term_catch_skip {body : CSimpl σ}
    (h_body : Terminates Γ body s) :
    Terminates Γ (.catch body .skip) s := by
  apply Terminates.catch
  · exact h_body
  · intro t _; exact Terminates.skip t

-- cond terminates if both branches terminate
private theorem term_cond {b : σ → Bool} {c₁ c₂ : CSimpl σ}
    (h₁ : Terminates Γ c₁ s) (h₂ : Terminates Γ c₂ s) :
    Terminates Γ (.cond b c₁ c₂) s := by
  cases hb : b s
  · exact Terminates.condFalse b c₁ c₂ s hb h₂
  · exact Terminates.condTrue b c₁ c₂ s hb h₁

-- seq where second always terminates
private theorem term_seq_always {c₁ c₂ : CSimpl σ}
    (h₁ : Terminates Γ c₁ s)
    (h₂ : ∀ (t : σ), Terminates Γ c₂ t) :
    Terminates Γ (.seq c₁ c₂) s := by
  apply Terminates.seq _ _ _ h₁
  intro t _; exact h₂ t

end Helpers

/-! # rb_capacity: catch(guard(seq(basic, throw)), skip) -/

theorem rb_capacity_terminates (Γ : ProcEnv ProgramState) (s : ProgramState) :
    Terminates Γ rb_capacity_body s := by
  unfold rb_capacity_body
  exact term_catch_skip (term_guard term_basic_throw)

/-! # rb_size: catch(guard(seq(basic, throw)), skip) -/

theorem rb_size_terminates (Γ : ProcEnv ProgramState) (s : ProgramState) :
    Terminates Γ rb_size_body s := by
  unfold rb_size_body
  exact term_catch_skip (term_guard term_basic_throw)

/-! # rb_remaining: catch(guard(guard(seq(basic, throw))), skip) -/

theorem rb_remaining_terminates (Γ : ProcEnv ProgramState) (s : ProgramState) :
    Terminates Γ rb_remaining_body s := by
  unfold rb_remaining_body
  exact term_catch_skip (term_guard (term_guard term_basic_throw))

/-! # rb_is_empty: catch(seq(cond(seq(basic,throw), skip), seq(basic,throw)), skip) -/

theorem rb_is_empty_terminates (Γ : ProcEnv ProgramState) (s : ProgramState) :
    Terminates Γ rb_is_empty_body s := by
  unfold rb_is_empty_body
  apply term_catch_skip
  apply Terminates.seq
  · exact term_cond term_basic_throw term_skip
  · intro t _; exact term_basic_throw

/-! # rb_is_full: same shape as rb_is_empty -/

theorem rb_is_full_terminates (Γ : ProcEnv ProgramState) (s : ProgramState) :
    Terminates Γ rb_is_full_body s := by
  unfold rb_is_full_body
  apply term_catch_skip
  apply Terminates.seq
  · exact term_cond term_basic_throw term_skip
  · intro t _; exact term_basic_throw

/-! # rb_stats_total_ops: catch(guard^4(seq(basic, throw)), skip) -/

theorem rb_stats_total_ops_terminates (Γ : ProcEnv ProgramState) (s : ProgramState) :
    Terminates Γ rb_stats_total_ops_body s := by
  unfold rb_stats_total_ops_body
  exact term_catch_skip (term_guard (term_guard (term_guard (term_guard term_basic_throw))))

/-! # rb_iter_has_next: catch(seq(cond(...), seq(basic, throw)), skip) -/

theorem rb_iter_has_next_terminates (Γ : ProcEnv ProgramState) (s : ProgramState) :
    Terminates Γ rb_iter_has_next_body s := by
  unfold rb_iter_has_next_body
  apply term_catch_skip
  apply Terminates.seq
  · exact term_cond term_basic_throw term_skip
  · intro t _; exact term_basic_throw

/-! # Demonstration: cHoareTotal from cHoare + Terminates

This shows the pattern for total correctness. Given:
1. A partial correctness proof (cHoare)
2. A termination proof (Terminates)
We get total correctness (cHoareTotal). -/

/-- Demonstration: total correctness for skip (simple case to show the pattern).
    For real ring_buffer functions, the partial correctness proof must
    discharge guard obligations (heapPtrValid), which requires meaningful
    preconditions. -/
example (Γ : ProcEnv Unit) :
    cHoareTotal Γ (fun _ => True) .skip (fun _ => True) (fun _ => True) := by
  constructor
  · -- Partial correctness
    intro s _ o h_exec; cases h_exec; trivial
  · -- Termination
    intro s _; exact Terminates.skip s

/-- Total correctness for seq(basic, throw) wrapped in catch-skip.
    This is the shape of all simple accessor functions. -/
example (Γ : ProcEnv Unit) (f : Unit → Unit) :
    cHoareTotal Γ (fun _ => True) (.catch (.seq (.basic f) .throw) .skip) (fun _ => True) (fun _ => True) := by
  constructor
  · -- Partial correctness
    intro s _ o h_exec
    cases h_exec with
    | catchNormal _ _ _ _ h₁ =>
      cases h₁ with
      | seqNormal _ _ _ _ _ h_b h_t => cases h_t
    | catchAbrupt _ _ _ _ _ h₁ h₂ =>
      cases h₂ with
      | skip => trivial
    | catchFault _ _ _ h₁ =>
      cases h₁ with
      | seqNormal _ _ _ _ _ h_b h_t => cases h_t
      | seqFault _ _ _ h_b => cases h_b
  · -- Termination
    intro s _
    apply term_catch_skip
    exact term_basic_throw

/-! # Summary of the termination pattern

To prove total correctness for a ring_buffer_ext function:

1. Prove `Terminates Γ <func>_body s` for all states s.
   - For loop-free functions: structural decomposition using helpers above.
   - For functions with while loops: provide a decreasing measure.

2. Prove `cHoare Γ P <func>_body Q A` (partial correctness).
   - Use L1corres_cHoare_bridge from the L1 lifting, or
   - Prove directly on the Exec relation.

3. Combine: `cHoareTotal Γ P <func>_body Q A` = (2) ∧ (1).

The key insight: termination is orthogonal to partial correctness.
You can prove them independently and combine. This is why Simpl
separates Terminates from Exec.
-/
