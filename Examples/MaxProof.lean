-- Hand-written CSimpl for max(a, b) and Hoare triple proof
--
-- This is the first end-to-end test: Phase 0 exit criterion 1.
-- C source: uint32_t max(uint32_t a, uint32_t b) { return a > b ? a : b; }

import Clift.CSemantics.HoareDef

set_option maxHeartbeats 400000

/-! # State type for max() -/

/-- State for the max function. -/
structure MaxState where
  a : UInt32
  b : UInt32
  ret_val : UInt32
  deriving Repr, DecidableEq

/-! # CSimpl encoding of max() -/

/-- The condition function: a > b. -/
def max_cond : MaxState → Bool := fun s => decide (s.a > s.b)

/-- The CSimpl encoding of: return a > b ? a : b
    return X desugars to: set ret_val := X; throw
    Function body wrapped in catch to convert throw -> normal. -/
def max_body : CSimpl MaxState :=
  .catch
    (.cond max_cond
      (.seq (.basic (fun s => { s with ret_val := s.a })) .throw)
      (.seq (.basic (fun s => { s with ret_val := s.b })) .throw))
    .skip

/-- Empty procedure environment. -/
def max_Γ : ProcEnv MaxState := ProcEnv.empty

/-! # Hoare triple proof -/

/-- Lemma: the inner body always produces an abrupt outcome (never normal, never fault).
    Both branches do: basic; throw. -/
private theorem max_inner_abrupt (s : MaxState) (o : Outcome MaxState)
    (hExec : Exec max_Γ
      (.cond max_cond
        (.seq (.basic (fun s => { s with ret_val := s.a })) .throw)
        (.seq (.basic (fun s => { s with ret_val := s.b })) .throw))
      s o) :
    ∃ t, o = .abrupt t := by
  cases hExec with
  | condTrue _ _ _ _ _ hcond hBranch =>
    cases hBranch with
    | seqNormal _ _ _ _ _ hBasic hThrow =>
      cases hBasic with
      | basic => cases hThrow with | throw => exact ⟨_, rfl⟩
    | seqAbrupt _ _ _ _ hBasic => cases hBasic
    | seqFault _ _ _ hBasic => cases hBasic
  | condFalse _ _ _ _ _ hcond hBranch =>
    cases hBranch with
    | seqNormal _ _ _ _ _ hBasic hThrow =>
      cases hBasic with
      | basic => cases hThrow with | throw => exact ⟨_, rfl⟩
    | seqAbrupt _ _ _ _ hBasic => cases hBasic
    | seqFault _ _ _ hBasic => cases hBasic

/-- Lemma: the abrupt state from the inner body has the right ret_val. -/
private theorem max_inner_post (s : MaxState) (t : MaxState)
    (hExec : Exec max_Γ
      (.cond max_cond
        (.seq (.basic (fun s => { s with ret_val := s.a })) .throw)
        (.seq (.basic (fun s => { s with ret_val := s.b })) .throw))
      s (.abrupt t)) :
    t.ret_val = (if s.a > s.b then s.a else s.b) ∧ t.a = s.a ∧ t.b = s.b := by
  cases hExec with
  | condTrue _ _ _ _ _ hcond hBranch =>
    cases hBranch with
    | seqNormal _ _ _ _ _ hBasic hThrow =>
      cases hBasic with
      | basic =>
        cases hThrow with
        | throw =>
          simp [max_cond, decide_eq_true_eq] at hcond
          simp [hcond]
    | seqAbrupt _ _ _ _ hBasic => cases hBasic
  | condFalse _ _ _ _ _ hcond hBranch =>
    cases hBranch with
    | seqNormal _ _ _ _ _ hBasic hThrow =>
      cases hBasic with
      | basic =>
        cases hThrow with
        | throw =>
          -- hcond : max_cond s = false, which means decide (s.a > s.b) = false
          -- We need to show: ¬(s.a > s.b)
          unfold max_cond at hcond
          have hle : ¬(s.a > s.b) := by
            rw [decide_eq_false_iff_not] at hcond
            exact hcond
          simp [hle]
    | seqAbrupt _ _ _ _ hBasic => cases hBasic

/-- max_correct: partial correctness of max.
    For all inputs, ret_val = max(a, b) and inputs are unchanged. -/
theorem max_correct (a₀ b₀ : UInt32) :
    cHoare max_Γ
      (fun s => s.a = a₀ ∧ s.b = b₀)
      max_body
      (fun s => s.ret_val = (if a₀ > b₀ then a₀ else b₀) ∧ s.a = a₀ ∧ s.b = b₀)
      (fun _ => True) := by
  intro s ⟨ha, hb⟩ o hExec
  subst ha; subst hb
  unfold max_body at hExec
  cases hExec with
  | catchNormal _ _ _ _ hBody =>
    -- Body returned normally: impossible, both branches throw
    obtain ⟨t, ht⟩ := max_inner_abrupt s (.normal _) hBody
    cases ht  -- contradiction: .normal ≠ .abrupt
  | catchAbrupt _ _ _ _ _ hBody hHandler =>
    -- Body threw, handler ran. This is the normal execution path.
    obtain ⟨hRet, hA, hB⟩ := max_inner_post s _ hBody
    -- Handler is skip: preserves state
    cases hHandler with
    | skip => exact ⟨hRet, hA, hB⟩
  | catchFault _ _ _ hBody =>
    -- Body faulted: impossible, no guards
    obtain ⟨t, ht⟩ := max_inner_abrupt s .fault hBody
    cases ht  -- contradiction: .fault ≠ .abrupt

/-! # Total correctness -/

/-- max terminates from every state. -/
theorem max_terminates (s : MaxState) : Terminates max_Γ max_body s := by
  unfold max_body max_cond
  apply Terminates.catch
  · by_cases h : (fun s => decide (s.a > s.b)) s = true
    · exact Terminates.condTrue _ _ _ _ h
        (Terminates.seq _ _ s (Terminates.basic _ s) (fun t _ => Terminates.throw t))
    · have hf : (fun s => decide (s.a > s.b)) s = false := by
        simp [Bool.eq_false_iff] at h ⊢; exact h
      exact Terminates.condFalse _ _ _ _ hf
        (Terminates.seq _ _ s (Terminates.basic _ s) (fun t _ => Terminates.throw t))
  · intro t _; exact Terminates.skip t

/-- Total correctness of max. -/
theorem max_total_correct (a₀ b₀ : UInt32) :
    cHoareTotal max_Γ
      (fun s => s.a = a₀ ∧ s.b = b₀)
      max_body
      (fun s => s.ret_val = (if a₀ > b₀ then a₀ else b₀) ∧ s.a = a₀ ∧ s.b = b₀)
      (fun _ => True) :=
  ⟨max_correct a₀ b₀, fun s _ => max_terminates s⟩
