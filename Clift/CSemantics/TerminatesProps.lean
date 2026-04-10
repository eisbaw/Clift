-- Properties of the Terminates predicate
--
-- Key theorem: Terminates_implies_Exec
-- If a program terminates, there exists some outcome.
-- This connects the Terminates predicate to the Exec relation
-- and is essential for total correctness: cHoareTotal = cHoare + Terminates.
--
-- Reference: Simpl Termination.thy, specifically `terminates_implies_exec`

import Clift.CSemantics.HoareDef

set_option maxHeartbeats 1600000

/-! # Terminates implies the existence of an Exec derivation -/

/-- If a program terminates from state s, then there exists an outcome o
    such that Exec Γ c s o. This is the key link between the Terminates
    predicate and the Exec relation.

    Proof: by induction on the Terminates derivation. -/
theorem Terminates_implies_Exec {σ : Type} {Γ : ProcEnv σ}
    {c : CSimpl σ} {s : σ} (h : Terminates Γ c s) :
    ∃ o, Exec Γ c s o := by
  induction h with
  | skip s => exact ⟨.normal s, Exec.skip s⟩
  | basic f s => exact ⟨.normal (f s), Exec.basic f s⟩
  | seq c₁ c₂ s _h_t₁ _h_t₂ ih₁ ih₂ =>
    -- ih₁ : ∃ o, Exec Γ c₁ s o
    -- ih₂ : ∀ t, Exec Γ c₁ s (.normal t) → ∃ o, Exec Γ c₂ t o
    obtain ⟨o₁, h_exec₁⟩ := ih₁
    match o₁ with
    | .normal t =>
      obtain ⟨o₂, h_exec₂⟩ := ih₂ t h_exec₁
      exact ⟨o₂, Exec.seqNormal c₁ c₂ s t o₂ h_exec₁ h_exec₂⟩
    | .abrupt t =>
      exact ⟨.abrupt t, Exec.seqAbrupt c₁ c₂ s t h_exec₁⟩
    | .fault =>
      exact ⟨.fault, Exec.seqFault c₁ c₂ s h_exec₁⟩
  | condTrue b c₁ c₂ s hb _h_t₁ ih₁ =>
    obtain ⟨o, h_exec⟩ := ih₁
    exact ⟨o, Exec.condTrue b c₁ c₂ s o hb h_exec⟩
  | condFalse b c₁ c₂ s hb _h_t₂ ih₂ =>
    obtain ⟨o, h_exec⟩ := ih₂
    exact ⟨o, Exec.condFalse b c₁ c₂ s o hb h_exec⟩
  | whileFalse b c s hb =>
    exact ⟨.normal s, Exec.whileFalse b c s hb⟩
  | whileTrue b c s hb _h_body _h_cont ih_body ih_cont =>
    -- ih_body : ∃ o, Exec Γ c s o
    -- ih_cont : ∀ t, Exec Γ c s (.normal t) → ∃ o, Exec Γ (.while b c) t o
    obtain ⟨o_body, h_exec_body⟩ := ih_body
    match o_body with
    | .normal t =>
      obtain ⟨o_loop, h_exec_loop⟩ := ih_cont t h_exec_body
      exact ⟨o_loop, Exec.whileTrue b c s t o_loop hb h_exec_body h_exec_loop⟩
    | .abrupt t =>
      exact ⟨.abrupt t, Exec.whileAbrupt b c s t hb h_exec_body⟩
    | .fault =>
      exact ⟨.fault, Exec.whileFault b c s hb h_exec_body⟩
  | callDefined p body s h_lookup _h_body ih_body =>
    obtain ⟨o, h_exec⟩ := ih_body
    exact ⟨o, Exec.callDefined p body s o h_lookup h_exec⟩
  | callUndefined p s h_lookup =>
    exact ⟨.fault, Exec.callUndefined p s h_lookup⟩
  | guardOk pred c s h_pred _h_body ih_body =>
    obtain ⟨o, h_exec⟩ := ih_body
    exact ⟨o, Exec.guardOk pred c s o h_pred h_exec⟩
  | guardFault pred c s h_not_pred =>
    exact ⟨.fault, Exec.guardFault pred c s h_not_pred⟩
  | throw s =>
    exact ⟨.abrupt s, Exec.throw s⟩
  | «catch» c₁ c₂ s _h_t₁ _h_t₂ ih₁ ih₂ =>
    -- ih₁ : ∃ o, Exec Γ c₁ s o
    -- ih₂ : ∀ t, Exec Γ c₁ s (.abrupt t) → ∃ o, Exec Γ c₂ t o
    obtain ⟨o₁, h_exec₁⟩ := ih₁
    match o₁ with
    | .normal t =>
      exact ⟨.normal t, Exec.catchNormal c₁ c₂ s t h_exec₁⟩
    | .abrupt t =>
      obtain ⟨o₂, h_exec₂⟩ := ih₂ t h_exec₁
      exact ⟨o₂, Exec.catchAbrupt c₁ c₂ s t o₂ h_exec₁ h_exec₂⟩
    | .fault =>
      exact ⟨.fault, Exec.catchFault c₁ c₂ s h_exec₁⟩
  | spec rel s =>
    by_cases h : ∃ t, rel s t
    · obtain ⟨t, h_rel⟩ := h
      exact ⟨.normal t, Exec.specNormal rel s t h_rel⟩
    · have h_stuck : ∀ t, ¬ rel s t := fun t ht => h ⟨t, ht⟩
      exact ⟨.fault, Exec.specStuck rel s h_stuck⟩
  | dynCom f s _h_body ih_body =>
    obtain ⟨o, h_exec⟩ := ih_body
    exact ⟨o, Exec.dynCom f s o h_exec⟩

/-! # Convenience lemmas for building Terminates proofs -/

/-- If a guard's predicate holds and the body terminates, the guarded command terminates.
    Decidable version for automated proofs. -/
theorem Terminates_guard_of_decidable {σ : Type} {Γ : ProcEnv σ}
    {pred : σ → Prop} {c : CSimpl σ} {s : σ} [Decidable (pred s)]
    (h_body : Terminates Γ c s) :
    Terminates Γ (.guard pred c) s := by
  cases (inferInstance : Decidable (pred s)) with
  | isTrue h => exact Terminates.guardOk pred c s h h_body
  | isFalse h => exact Terminates.guardFault pred c s h

/-- catch terminates when body terminates and handler terminates for all abrupt states. -/
theorem Terminates_catch {σ : Type} {Γ : ProcEnv σ}
    {c₁ c₂ : CSimpl σ} {s : σ}
    (h₁ : Terminates Γ c₁ s)
    (h₂ : ∀ t, Exec Γ c₁ s (.abrupt t) → Terminates Γ c₂ t) :
    Terminates Γ (.catch c₁ c₂) s :=
  Terminates.catch c₁ c₂ s h₁ h₂

/-- seq terminates when first terminates and second terminates for all normal outcomes. -/
theorem Terminates_seq {σ : Type} {Γ : ProcEnv σ}
    {c₁ c₂ : CSimpl σ} {s : σ}
    (h₁ : Terminates Γ c₁ s)
    (h₂ : ∀ t, Exec Γ c₁ s (.normal t) → Terminates Γ c₂ t) :
    Terminates Γ (.seq c₁ c₂) s :=
  Terminates.seq c₁ c₂ s h₁ h₂

/-! # cHoareTotal equivalence -/

/-- cHoareTotal unfolds to cHoare + Terminates (by definition). -/
theorem cHoareTotal_iff {σ : Type} {Γ : ProcEnv σ}
    {P : σ → Prop} {c : CSimpl σ} {Q A : σ → Prop} :
    cHoareTotal Γ P c Q A ↔ (cHoare Γ P c Q A ∧ ∀ s, P s → Terminates Γ c s) := by
  rfl

/-! # Total correctness implies at least one outcome exists -/

/-- Total correctness means: for every state satisfying P, there exists
    an outcome, and that outcome is either normal (satisfying Q) or abrupt
    (satisfying A), but never fault. -/
theorem cHoareTotal_implies_exists_outcome {σ : Type} {Γ : ProcEnv σ}
    {P : σ → Prop} {c : CSimpl σ} {Q A : σ → Prop}
    (h : cHoareTotal Γ P c Q A) (s : σ) (hP : P s) :
    ∃ o, Exec Γ c s o ∧ match o with
      | .normal t => Q t
      | .abrupt t => A t
      | .fault => False := by
  obtain ⟨h_hoare, h_term⟩ := h
  have h_terminates := h_term s hP
  obtain ⟨o, h_exec⟩ := Terminates_implies_Exec h_terminates
  exact ⟨o, h_exec, h_hoare s hP o h_exec⟩
