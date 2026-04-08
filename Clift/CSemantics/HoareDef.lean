-- Hoare triple definitions for CSimpl, directly on the Exec relation
--
-- Following Simpl's HoarePartialDef.thy: define partial and total correctness
-- Hoare triples in terms of the Exec inductive relation.
--
-- These are the CSimpl-level Hoare triples. The NondetM-level Hoare triples
-- (validHoare/totalHoare) are used after L1 lifting (SimplConv).
-- The two are connected by the ccorres correspondence.
--
-- Reference: ext/AutoCorres2/c-parser/Simpl/HoarePartialDef.thy

import Clift.CSemantics.Exec

/-! # Partial correctness Hoare triple for CSimpl -/

/-- Partial correctness Hoare triple for CSimpl.

    `cHoare Γ P c Q A` means: for every initial state satisfying `P`,
    if execution of `c` in environment `Γ` terminates, then:
    - Normal outcomes satisfy `Q`
    - Abrupt outcomes satisfy `A`
    - Fault never occurs

    This follows Simpl's `\<Gamma> \<turnstile> {P} c {Q},{A}` from HoarePartialDef.thy.

    The abrupt postcondition `A` is needed because CSimpl uses throw/catch
    for return statements. In max(), the catch wrapper handles the return,
    so `A` will typically be `fun _ => True` for the inner body.

    Note: partial correctness means non-termination is OK (no derivation
    of Exec exists, so the universal quantifier over outcomes is vacuously true). -/
def cHoare {σ : Type} (Γ : ProcEnv σ) (P : σ → Prop) (c : CSimpl σ)
    (Q : σ → Prop) (A : σ → Prop) : Prop :=
  ∀ s, P s → ∀ o, Exec Γ c s o →
    match o with
    | .normal t => Q t
    | .abrupt t => A t
    | .fault    => False

/-- Total correctness Hoare triple for CSimpl.

    `cHoareTotal Γ P c Q A` means: partial correctness AND the
    command terminates from every state satisfying P.

    Following Simpl's `\<Gamma> \<turnstile>\<^sub>t {P} c {Q},{A}`. -/
def cHoareTotal {σ : Type} (Γ : ProcEnv σ) (P : σ → Prop) (c : CSimpl σ)
    (Q : σ → Prop) (A : σ → Prop) : Prop :=
  cHoare Γ P c Q A ∧
  ∀ s, P s → Terminates Γ c s

/-! # Simplified variant: no abrupt allowed -/

/-- Simplified Hoare triple that forbids abrupt outcomes.
    Useful for straight-line code with no throw/return. -/
def cHoareNoAbrupt {σ : Type} (Γ : ProcEnv σ) (P : σ → Prop)
    (c : CSimpl σ) (Q : σ → Prop) : Prop :=
  cHoare Γ P c Q (fun _ => False)

/-! # Basic Hoare rules for CSimpl -/

/-- Skip rule: {P} skip {P} -/
theorem cHoare_skip {σ : Type} (Γ : ProcEnv σ) (P : σ → Prop) :
    cHoare Γ P .skip P (fun _ => True) := by
  intro s hP o hExec
  cases hExec with
  | skip => exact hP

/-- Basic rule: {Q ∘ f} basic f {Q} -/
theorem cHoare_basic {σ : Type} (Γ : ProcEnv σ) (f : σ → σ) (Q : σ → Prop) :
    cHoare Γ (fun s => Q (f s)) (.basic f) Q (fun _ => True) := by
  intro s hP o hExec
  cases hExec with
  | basic => exact hP

/-- Seq rule: if {P} c1 {R} and {R} c2 {Q}, then {P} c1;c2 {Q} -/
theorem cHoare_seq {σ : Type} (Γ : ProcEnv σ) {P R Q A : σ → Prop}
    {c₁ c₂ : CSimpl σ}
    (h₁ : cHoare Γ P c₁ R A)
    (h₂ : cHoare Γ R c₂ Q A) :
    cHoare Γ P (.seq c₁ c₂) Q A := by
  intro s hP o hExec
  cases hExec with
  | seqNormal _ _ _ _ _ h_exec₁ h_exec₂ =>
    have hR := h₁ s hP (.normal _) h_exec₁
    exact h₂ _ hR o h_exec₂
  | seqAbrupt _ _ _ _ h_exec₁ =>
    exact h₁ s hP (.abrupt _) h_exec₁
  | seqFault _ _ _ h_exec₁ =>
    exact h₁ s hP .fault h_exec₁

/-- Cond rule: if {P ∧ b} c₁ {Q} and {P ∧ ¬b} c₂ {Q}, then {P} cond b c₁ c₂ {Q} -/
theorem cHoare_cond {σ : Type} (Γ : ProcEnv σ) {P Q A : σ → Prop}
    {b : σ → Bool} {c₁ c₂ : CSimpl σ}
    (h₁ : cHoare Γ (fun s => P s ∧ b s = true) c₁ Q A)
    (h₂ : cHoare Γ (fun s => P s ∧ b s = false) c₂ Q A) :
    cHoare Γ P (.cond b c₁ c₂) Q A := by
  intro s hP o hExec
  cases hExec with
  | condTrue _ _ _ _ _ hb hExec_body =>
    exact h₁ s ⟨hP, hb⟩ o hExec_body
  | condFalse _ _ _ _ _ hb hExec_body =>
    exact h₂ s ⟨hP, hb⟩ o hExec_body

/-- Consequence rule: strengthen pre, weaken post -/
theorem cHoare_consequence {σ : Type} (Γ : ProcEnv σ)
    {P P' Q Q' A A' : σ → Prop} {c : CSimpl σ}
    (hP : ∀ s, P' s → P s)
    (hQ : ∀ s, Q s → Q' s)
    (hA : ∀ s, A s → A' s)
    (h : cHoare Γ P c Q A) :
    cHoare Γ P' c Q' A' := by
  intro s hP' o hExec
  have := h s (hP s hP') o hExec
  match o with
  | .normal t => exact hQ t this
  | .abrupt t => exact hA t this
  | .fault => exact this

/-- Guard rule: if P implies the guard and {P} c {Q}, then {P} guard g c {Q} -/
theorem cHoare_guard {σ : Type} (Γ : ProcEnv σ)
    {P Q A : σ → Prop} {g : σ → Prop} {c : CSimpl σ}
    (hg : ∀ s, P s → g s)
    (h : cHoare Γ P c Q A) :
    cHoare Γ P (.guard g c) Q A := by
  intro s hP o hExec
  cases hExec with
  | guardOk _ _ _ _ hg_ok hExec_body =>
    exact h s hP o hExec_body
  | guardFault _ _ _ hg_fail =>
    exact absurd (hg s hP) hg_fail

/-- Throw rule: {A} throw {Q},{A} — throw always produces abrupt -/
theorem cHoare_throw {σ : Type} (Γ : ProcEnv σ) (A : σ → Prop) :
    cHoare Γ A .throw (fun _ => True) A := by
  intro s hA o hExec
  cases hExec with
  | throw => exact hA

/-- Catch rule -/
theorem cHoare_catch {σ : Type} (Γ : ProcEnv σ)
    {P Q A B : σ → Prop} {c₁ c₂ : CSimpl σ}
    (h₁ : cHoare Γ P c₁ Q A)
    (h₂ : cHoare Γ A c₂ Q B) :
    cHoare Γ P (.catch c₁ c₂) Q B := by
  intro s hP o hExec
  cases hExec with
  | catchNormal _ _ _ _ h_exec₁ =>
    exact h₁ s hP (.normal _) h_exec₁
  | catchAbrupt _ _ _ _ _ h_exec₁ h_exec₂ =>
    have hA := h₁ s hP (.abrupt _) h_exec₁
    exact h₂ _ hA o h_exec₂
  | catchFault _ _ _ h_exec₁ =>
    exact h₁ s hP .fault h_exec₁

/-- DynCom rule: if the Hoare triple holds for every possible command f s can produce -/
theorem cHoare_dynCom {σ : Type} (Γ : ProcEnv σ)
    {P Q A : σ → Prop} {f : σ → CSimpl σ}
    (h : ∀ s, P s → cHoare Γ P (f s) Q A) :
    cHoare Γ P (.dynCom f) Q A := by
  intro s hP o hExec
  cases hExec with
  | dynCom _ _ _ h_exec_body =>
    exact h s hP s hP o h_exec_body
