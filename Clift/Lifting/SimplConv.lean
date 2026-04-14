-- L1: CSimpl -> NondetM shallow monadic embedding + corres proof
--
-- Design: ADR-001 (backlog/docs/adr-001-l1-exception-encoding.md)
-- Reference: ext/AutoCorres2/L1Defs.thy
--
-- Exception encoding (following seL4):
--   Normal outcome -> Except.ok ()
--   Abrupt outcome -> Except.error ()
--   Fault -> NondetM failure (failed flag)

import Clift.CSemantics
import Clift.MonadLib

set_option maxHeartbeats 1600000

/-! # L1 Monad type -/

abbrev L1Monad (σ : Type) := NondetM σ (Except Unit Unit)

/-! # L1 combinators -/

namespace L1

variable {σ : Type}

def skip : L1Monad σ := NondetM.pure (Except.ok ())

def modify (f : σ → σ) : L1Monad σ :=
  fun s => { results := {(Except.ok (), f s)}, failed := False }

def throw : L1Monad σ := NondetM.pure (Except.error ())

def guard (p : σ → Prop) [DecidablePred p] : L1Monad σ :=
  fun s => if p s
    then { results := {(Except.ok (), s)}, failed := False }
    else { results := ∅, failed := True }

def seq (m₁ m₂ : L1Monad σ) : L1Monad σ :=
  fun s =>
    let r₁ := m₁ s
    { results := (fun p => ∃ s', (Except.ok (), s') ∈ r₁.results ∧ p ∈ (m₂ s').results) ∪
                 (fun p => (Except.error (), p.2) ∈ r₁.results ∧ p.1 = Except.error ())
      failed := r₁.failed ∨ ∃ s', (Except.ok (), s') ∈ r₁.results ∧ (m₂ s').failed }

def condition (c : σ → Bool) (t e : L1Monad σ) : L1Monad σ :=
  fun s => if c s then t s else e s

def «catch» (body handler : L1Monad σ) : L1Monad σ :=
  fun s =>
    let r := body s
    { results := (fun p => (Except.ok (), p.2) ∈ r.results ∧ p.1 = Except.ok ()) ∪
                 (fun p => ∃ s', (Except.error (), s') ∈ r.results ∧ p ∈ (handler s').results)
      failed := r.failed ∨ ∃ s', (Except.error (), s') ∈ r.results ∧ (handler s').failed }

inductive WhileResult (c : σ → Bool) (body : L1Monad σ) : σ → Except Unit Unit × σ → Prop where
  | done (s : σ) (hc : c s = false) :
      WhileResult c body s (Except.ok (), s)
  | step (s s' : σ) (p : Except Unit Unit × σ) (hc : c s = true)
      (h_body : (Except.ok (), s') ∈ (body s).results)
      (h_rest : WhileResult c body s' p) :
      WhileResult c body s p
  | abrupt (s s' : σ) (hc : c s = true)
      (h_body : (Except.error (), s') ∈ (body s).results) :
      WhileResult c body s (Except.error (), s')

inductive WhileFail (c : σ → Bool) (body : L1Monad σ) : σ → Prop where
  | here (s : σ) (hc : c s = true) (h_fail : (body s).failed) :
      WhileFail c body s
  | later (s s' : σ) (hc : c s = true)
      (h_body : (Except.ok (), s') ∈ (body s).results)
      (h_rest : WhileFail c body s') :
      WhileFail c body s

def «while» (c : σ → Bool) (body : L1Monad σ) : L1Monad σ :=
  fun s =>
    { results := fun p => WhileResult c body s p
      failed := WhileFail c body s }

def spec (rel : σ → σ → Prop) : L1Monad σ :=
  fun s =>
    { results := fun p => ∃ t, rel s t ∧ p = (Except.ok (), t)
      failed := ¬ ∃ t, rel s t }

def fail : L1Monad σ :=
  fun _ => { results := ∅, failed := True }

/-- L1 procedure environment: maps procedure names to L1 monadic bodies.
    Parallel to ProcEnv which maps names to CSimpl bodies. -/
abbrev L1ProcEnv (σ : Type) := ProcName → Option (L1Monad σ)

namespace L1ProcEnv

variable {σ : Type}

/-- Empty L1 procedure environment (no procedures defined). -/
def empty : L1ProcEnv σ := fun _ => none

/-- Extend an L1 procedure environment with a new binding. -/
def insert (Γ : L1ProcEnv σ) (name : ProcName) (body : L1Monad σ) : L1ProcEnv σ :=
  fun n => if n == name then some body else Γ n

end L1ProcEnv

/-- L1.call: look up a procedure in the L1 procedure environment and execute it.
    Fails if the procedure is not found (matching CSimpl.call → Exec.callUndefined → fault). -/
def call (l1Γ : L1ProcEnv σ) (name : ProcName) : L1Monad σ :=
  match l1Γ name with
  | some body => body
  | none => L1.fail

/-- L1.dynCom: execute a state-dependent L1 monadic command.
    Given a function from state to L1Monad, evaluate it at the current state. -/
def dynCom (f : σ → L1Monad σ) : L1Monad σ :=
  fun s => f s s

end L1

/-! # L1corres -/

-- L1corres: if the L1 monad doesn't fail, every CSimpl Exec outcome
-- is captured: normal -> ok result, abrupt -> error result, fault -> impossible.

def L1corres {σ : Type} (Γ : ProcEnv σ) (m : L1Monad σ) (c : CSimpl σ) : Prop :=
  ∀ s, ¬(m s).failed →
    (∀ s', Exec Γ c s (.normal s') → (Except.ok (), s') ∈ (m s).results) ∧
    (∀ s', Exec Γ c s (.abrupt s') → (Except.error (), s') ∈ (m s).results) ∧
    (¬ Exec Γ c s .fault)

/-! # L1corres lemmas -/

theorem L1corres_skip {σ : Type} (Γ : ProcEnv σ) :
    L1corres Γ L1.skip (.skip : CSimpl σ) := by
  intro s _; refine ⟨?_, ?_, ?_⟩
  · intro s' h; cases h; rfl
  · intro s' h; cases h
  · intro h; cases h

theorem L1corres_basic {σ : Type} (Γ : ProcEnv σ) (f : σ → σ) :
    L1corres Γ (L1.modify f) (.basic f : CSimpl σ) := by
  intro s _; refine ⟨?_, ?_, ?_⟩
  · intro s' h; cases h; rfl
  · intro s' h; cases h
  · intro h; cases h

theorem L1corres_throw {σ : Type} (Γ : ProcEnv σ) :
    L1corres Γ L1.throw (.throw : CSimpl σ) := by
  intro s _; refine ⟨?_, ?_, ?_⟩
  · intro s' h; cases h
  · intro s' h; cases h; rfl
  · intro h; cases h

/-! ## Helper: L1.seq failure propagation

When `L1.seq m₁ m₂` does not fail at state s, we can conclude:
- m₁ does not fail at s
- For every ok-result s' of m₁ at s, m₂ does not fail at s'
-/
private theorem L1_seq_not_failed_left {σ : Type} {m₁ m₂ : L1Monad σ} {s : σ}
    (h : ¬(L1.seq m₁ m₂ s).failed) : ¬(m₁ s).failed := by
  intro hf
  apply h
  simp only [L1.seq]
  exact Or.inl hf

private theorem L1_seq_not_failed_right {σ : Type} {m₁ m₂ : L1Monad σ} {s s' : σ}
    (h : ¬(L1.seq m₁ m₂ s).failed)
    (h_mem : (Except.ok (), s') ∈ (m₁ s).results) : ¬(m₂ s').failed := by
  intro hf
  apply h
  simp only [L1.seq]
  exact Or.inr ⟨s', h_mem, hf⟩

/-! ## L1corres_seq -/

theorem L1corres_seq {σ : Type} (Γ : ProcEnv σ) {m₁ m₂ : L1Monad σ} {c₁ c₂ : CSimpl σ}
    (h₁ : L1corres Γ m₁ c₁) (h₂ : L1corres Γ m₂ c₂) :
    L1corres Γ (L1.seq m₁ m₂) (.seq c₁ c₂) := by
  intro s h_nf
  have h_nf₁ : ¬(m₁ s).failed := L1_seq_not_failed_left h_nf
  obtain ⟨h₁_ok, h₁_err, h₁_fault⟩ := h₁ s h_nf₁
  refine ⟨?_, ?_, ?_⟩
  · -- Normal case: Exec Γ (.seq c₁ c₂) s (.normal s')
    intro s' h_exec
    cases h_exec with
    | seqNormal _ _ _ t _ h_c₁ h_c₂ =>
      have h_m₁_t := h₁_ok t h_c₁
      have h_nf₂ : ¬(m₂ t).failed := L1_seq_not_failed_right h_nf h_m₁_t
      obtain ⟨h₂_ok, _, _⟩ := h₂ t h_nf₂
      simp only [L1.seq]
      exact Set.mem_union_left _ ⟨t, h_m₁_t, h₂_ok s' h_c₂⟩
  · -- Abrupt case: Exec Γ (.seq c₁ c₂) s (.abrupt s')
    intro s' h_exec
    cases h_exec with
    | seqAbrupt _ _ _ _ h_c₁ =>
      have h_m₁_err := h₁_err s' h_c₁
      simp only [L1.seq]
      exact Set.mem_union_right _ ⟨h_m₁_err, rfl⟩
    | seqNormal _ _ _ t _ h_c₁ h_c₂ =>
      have h_m₁_t := h₁_ok t h_c₁
      have h_nf₂ : ¬(m₂ t).failed := L1_seq_not_failed_right h_nf h_m₁_t
      obtain ⟨_, h₂_err, _⟩ := h₂ t h_nf₂
      simp only [L1.seq]
      exact Set.mem_union_left _ ⟨t, h_m₁_t, h₂_err s' h_c₂⟩
  · -- Fault case: no fault possible
    intro h_exec
    cases h_exec with
    | seqFault _ _ _ h_c₁_fault =>
      exact h₁_fault h_c₁_fault
    | seqNormal _ _ _ t _ h_c₁ h_c₂ =>
      have h_m₁_t := h₁_ok t h_c₁
      have h_nf₂ : ¬(m₂ t).failed := L1_seq_not_failed_right h_nf h_m₁_t
      obtain ⟨_, _, h₂_fault⟩ := h₂ t h_nf₂
      exact h₂_fault h_c₂

/-! ## L1corres_cond -/

theorem L1corres_cond {σ : Type} (Γ : ProcEnv σ) {b : σ → Bool}
    {m₁ m₂ : L1Monad σ} {c₁ c₂ : CSimpl σ}
    (h₁ : L1corres Γ m₁ c₁) (h₂ : L1corres Γ m₂ c₂) :
    L1corres Γ (L1.condition b m₁ m₂) (.cond b c₁ c₂) := by
  intro s h_nf
  simp only [L1.condition] at h_nf ⊢
  cases hb : b s with
  | true =>
    simp [hb] at h_nf ⊢
    obtain ⟨h₁_ok, h₁_err, h₁_fault⟩ := h₁ s h_nf
    refine ⟨?_, ?_, ?_⟩
    · intro s' h_exec
      cases h_exec with
      | condTrue _ _ _ _ _ hb' h_c₁ => exact h₁_ok s' h_c₁
      | condFalse _ _ _ _ _ hb' => simp [hb] at hb'
    · intro s' h_exec
      cases h_exec with
      | condTrue _ _ _ _ _ hb' h_c₁ => exact h₁_err s' h_c₁
      | condFalse _ _ _ _ _ hb' => simp [hb] at hb'
    · intro h_exec
      cases h_exec with
      | condTrue _ _ _ _ _ hb' h_c₁ => exact h₁_fault h_c₁
      | condFalse _ _ _ _ _ hb' => simp [hb] at hb'
  | false =>
    simp [hb] at h_nf ⊢
    obtain ⟨h₂_ok, h₂_err, h₂_fault⟩ := h₂ s h_nf
    refine ⟨?_, ?_, ?_⟩
    · intro s' h_exec
      cases h_exec with
      | condTrue _ _ _ _ _ hb' => simp [hb] at hb'
      | condFalse _ _ _ _ _ hb' h_c₂ => exact h₂_ok s' h_c₂
    · intro s' h_exec
      cases h_exec with
      | condTrue _ _ _ _ _ hb' => simp [hb] at hb'
      | condFalse _ _ _ _ _ hb' h_c₂ => exact h₂_err s' h_c₂
    · intro h_exec
      cases h_exec with
      | condTrue _ _ _ _ _ hb' => simp [hb] at hb'
      | condFalse _ _ _ _ _ hb' h_c₂ => exact h₂_fault h_c₂

/-! ## L1corres_catch -/

/-- Helper: if L1.catch doesn't fail, the body doesn't fail -/
private theorem L1_catch_not_failed_body {σ : Type} {m₁ m₂ : L1Monad σ} {s : σ}
    (h : ¬(L1.catch m₁ m₂ s).failed) : ¬(m₁ s).failed := by
  intro hf; apply h; simp only [L1.catch]; exact Or.inl hf

private theorem L1_catch_not_failed_handler {σ : Type} {m₁ m₂ : L1Monad σ} {s s' : σ}
    (h : ¬(L1.catch m₁ m₂ s).failed)
    (h_mem : (Except.error (), s') ∈ (m₁ s).results) : ¬(m₂ s').failed := by
  intro hf; apply h; simp only [L1.catch]; exact Or.inr ⟨s', h_mem, hf⟩

theorem L1corres_catch {σ : Type} (Γ : ProcEnv σ)
    {m₁ m₂ : L1Monad σ} {c₁ c₂ : CSimpl σ}
    (h₁ : L1corres Γ m₁ c₁) (h₂ : L1corres Γ m₂ c₂) :
    L1corres Γ (L1.catch m₁ m₂) (.catch c₁ c₂) := by
  intro s h_nf
  have h_nf₁ : ¬(m₁ s).failed := L1_catch_not_failed_body h_nf
  obtain ⟨h₁_ok, h₁_err, h₁_fault⟩ := h₁ s h_nf₁
  refine ⟨?_, ?_, ?_⟩
  · -- Normal: catchNormal or catchAbrupt where handler returns normal
    intro s' h_exec
    cases h_exec with
    | catchNormal _ _ _ _ h_c₁ =>
      simp only [L1.catch]
      exact Set.mem_union_left _ ⟨h₁_ok s' h_c₁, rfl⟩
    | catchAbrupt _ _ _ t _ h_c₁ h_c₂ =>
      have h_m₁_err := h₁_err t h_c₁
      have h_nf₂ := L1_catch_not_failed_handler h_nf h_m₁_err
      obtain ⟨h₂_ok, _, _⟩ := h₂ t h_nf₂
      simp only [L1.catch]
      exact Set.mem_union_right _ ⟨t, h_m₁_err, h₂_ok s' h_c₂⟩
  · -- Abrupt: from catchAbrupt where handler returns abrupt
    intro s' h_exec
    cases h_exec with
    | catchAbrupt _ _ _ t _ h_c₁ h_c₂ =>
      have h_m₁_err := h₁_err t h_c₁
      have h_nf₂ := L1_catch_not_failed_handler h_nf h_m₁_err
      obtain ⟨_, h₂_err, _⟩ := h₂ t h_nf₂
      simp only [L1.catch]
      exact Set.mem_union_right _ ⟨t, h_m₁_err, h₂_err s' h_c₂⟩
  · -- Fault: not possible
    intro h_exec
    cases h_exec with
    | catchFault _ _ _ h_c₁_fault => exact h₁_fault h_c₁_fault
    | catchAbrupt _ _ _ t _ h_c₁ h_c₂ =>
      have h_m₁_err := h₁_err t h_c₁
      have h_nf₂ := L1_catch_not_failed_handler h_nf h_m₁_err
      obtain ⟨_, _, h₂_fault⟩ := h₂ t h_nf₂
      exact h₂_fault h_c₂

/-! ## L1corres_guard -/

theorem L1corres_guard {σ : Type} (Γ : ProcEnv σ)
    {m : L1Monad σ} {c : CSimpl σ} {p : σ → Prop} [DecidablePred p]
    (hm : L1corres Γ m c) :
    L1corres Γ (L1.seq (L1.guard p) m) (.guard p c) := by
  intro s h_nf
  -- If ¬p s, the guard fails, making seq fail. But h_nf says seq doesn't fail.
  -- Therefore p s must hold.
  have hp : p s := by
    by_cases h_ps : p s
    · exact h_ps
    · exfalso; apply h_nf
      show (L1.seq (L1.guard p) m s).failed
      simp only [L1.seq, L1.guard]
      left
      simp [h_ps]
  -- With p s, the guard produces {(ok, s)} with failed = False.
  -- The seq then effectively passes through to m at s.
  have h_nf_m : ¬(m s).failed := by
    intro hf; apply h_nf
    show (L1.seq (L1.guard p) m s).failed
    simp only [L1.seq, L1.guard]
    right
    refine ⟨s, ?_, hf⟩
    show (Except.ok (), s) ∈ (L1.guard p s).results
    unfold L1.guard
    simp [hp]
  obtain ⟨hm_ok, hm_err, hm_fault⟩ := hm s h_nf_m
  -- When p s holds, L1.guard p at s produces {(ok, s)} with failed = False.
  -- So L1.seq (L1.guard p) m at s has same results as m at s (for the first set)
  -- and the second set (error pass-through from guard) is empty.
  have h_guard_simp : L1.guard p s =
      { results := {(Except.ok (), s)}, failed := False } := by
    simp [L1.guard, hp]
  refine ⟨?_, ?_, ?_⟩
  · intro s' h_exec
    cases h_exec with
    | guardOk _ _ _ _ _ h_c =>
      simp only [L1.seq, h_guard_simp]
      exact Set.mem_union_left _ ⟨s, rfl, hm_ok s' h_c⟩
  · intro s' h_exec
    cases h_exec with
    | guardOk _ _ _ _ _ h_c =>
      simp only [L1.seq, h_guard_simp]
      exact Set.mem_union_left _ ⟨s, rfl, hm_err s' h_c⟩
  · intro h_exec
    cases h_exec with
    | guardOk _ _ _ _ _ h_c => exact hm_fault h_c
    | guardFault _ _ _ h_np => exact absurd hp h_np

/-! ## L1corres_call

L1corres for CSimpl.call: if the procedure environment maps `name` to `body`,
and the L1 procedure environment maps `name` to `l1_body`, and L1corres holds
for `l1_body` / `body`, then L1.call has L1corres with CSimpl.call.

The key insight: we parametrize over an L1ProcEnv that mirrors the CSimpl ProcEnv.
The hypothesis requires L1corres for each procedure body looked up. -/

theorem L1corres_call {σ : Type} (Γ : ProcEnv σ) (l1Γ : L1.L1ProcEnv σ) (name : ProcName)
    (h_env : ∀ (p : ProcName) (body : CSimpl σ),
      Γ p = some body →
      ∃ l1_body, l1Γ p = some l1_body ∧ L1corres Γ l1_body body)
    (h_none : ∀ (p : ProcName), Γ p = none → l1Γ p = none) :
    L1corres Γ (L1.call l1Γ name) (.call name) := by
  intro s h_nf
  refine ⟨?_, ?_, ?_⟩
  · -- Normal case: Exec Γ (.call name) s (.normal s')
    intro s' h_exec
    cases h_exec with
    | callDefined _ body _ _ h_lookup h_body_exec =>
      obtain ⟨l1_body, h_l1_lookup, h_corres⟩ := h_env name body h_lookup
      show (Except.ok (), s') ∈ (L1.call l1Γ name s).results
      simp only [L1.call, h_l1_lookup]
      have h_nf' : ¬(l1_body s).failed := by
        rwa [show L1.call l1Γ name = l1_body from by simp [L1.call, h_l1_lookup]] at h_nf
      exact (h_corres s h_nf').1 s' h_body_exec
  · -- Abrupt case: Exec Γ (.call name) s (.abrupt s')
    intro s' h_exec
    cases h_exec with
    | callDefined _ body _ _ h_lookup h_body_exec =>
      obtain ⟨l1_body, h_l1_lookup, h_corres⟩ := h_env name body h_lookup
      show (Except.error (), s') ∈ (L1.call l1Γ name s).results
      simp only [L1.call, h_l1_lookup]
      have h_nf' : ¬(l1_body s).failed := by
        rwa [show L1.call l1Γ name = l1_body from by simp [L1.call, h_l1_lookup]] at h_nf
      exact (h_corres s h_nf').2.1 s' h_body_exec
  · -- Fault case: Exec Γ (.call name) s .fault
    intro h_exec
    cases h_exec with
    | callDefined _ body _ _ h_lookup h_body_exec =>
      obtain ⟨l1_body, h_l1_lookup, h_corres⟩ := h_env name body h_lookup
      have h_nf' : ¬(l1_body s).failed := by
        rwa [show L1.call l1Γ name = l1_body from by simp [L1.call, h_l1_lookup]] at h_nf
      exact (h_corres s h_nf').2.2 h_body_exec
    | callUndefined _ _ h_lookup =>
      have h_l1_none := h_none name h_lookup
      exact absurd (show (L1.call l1Γ name s).failed from by simp [L1.call, h_l1_none, L1.fail]) h_nf

/-! ## L1corres_call_single

Targeted version of L1corres_call: only requires the SPECIFIC callee to be
present in the L1ProcEnv, not ALL procedures in Gamma. This enables corres
proofs for calling functions even when the L1ProcEnv is not a complete mirror
of the CSimpl ProcEnv (e.g., incremental builds or partial environments).

The trade-off: if Gamma maps `name` to `none` (undefined call), this lemma
requires the caller to ensure `Gamma name = some body`. For well-formed
programs where every called function is defined, this always holds. -/

theorem L1corres_call_single {σ : Type} (Γ : ProcEnv σ) (l1Γ : L1.L1ProcEnv σ)
    (name : ProcName) (body : CSimpl σ) (l1_body : L1Monad σ)
    (h_gamma : Γ name = some body)
    (h_l1gamma : l1Γ name = some l1_body)
    (h_corres : L1corres Γ l1_body body) :
    L1corres Γ (L1.call l1Γ name) (.call name) := by
  intro s h_nf
  have h_nf' : ¬(l1_body s).failed := by
    rwa [show L1.call l1Γ name = l1_body from by simp [L1.call, h_l1gamma]] at h_nf
  obtain ⟨h_ok, h_err, h_fault⟩ := h_corres s h_nf'
  refine ⟨?_, ?_, ?_⟩
  · intro s' h_exec
    cases h_exec with
    | callDefined _ body' _ _ h_lookup h_body_exec =>
      have h_eq : body' = body := by
        have : some body' = some body := h_lookup ▸ h_gamma
        exact Option.some.inj this
      subst h_eq
      show (Except.ok (), s') ∈ (L1.call l1Γ name s).results
      simp only [L1.call, h_l1gamma]
      exact h_ok s' h_body_exec
  · intro s' h_exec
    cases h_exec with
    | callDefined _ body' _ _ h_lookup h_body_exec =>
      have h_eq : body' = body := by
        have : some body' = some body := h_lookup ▸ h_gamma
        exact Option.some.inj this
      subst h_eq
      show (Except.error (), s') ∈ (L1.call l1Γ name s).results
      simp only [L1.call, h_l1gamma]
      exact h_err s' h_body_exec
  · intro h_exec
    cases h_exec with
    | callDefined _ body' _ _ h_lookup h_body_exec =>
      have h_eq : body' = body := by
        have : some body' = some body := h_lookup ▸ h_gamma
        exact Option.some.inj this
      subst h_eq
      exact h_fault h_body_exec
    | callUndefined _ _ h_lookup =>
      simp [h_lookup] at h_gamma

/-! ## L1corres_dynCom

L1corres for CSimpl.dynCom: if for all states s, L1corres holds for
l1_f s / f s, then L1.dynCom l1_f has L1corres with CSimpl.dynCom f. -/

theorem L1corres_dynCom {σ : Type} (Γ : ProcEnv σ) {l1_f : σ → L1Monad σ} {f : σ → CSimpl σ}
    (h : ∀ s, L1corres Γ (l1_f s) (f s)) :
    L1corres Γ (L1.dynCom l1_f) (.dynCom f) := by
  intro s h_nf
  -- L1.dynCom l1_f at state s = l1_f s s
  -- h_nf : ¬(L1.dynCom l1_f s).failed = ¬(l1_f s s).failed
  have h_nf' : ¬(l1_f s s).failed := h_nf
  obtain ⟨h_ok, h_err, h_fault⟩ := h s s h_nf'
  refine ⟨?_, ?_, ?_⟩
  · intro s' h_exec
    cases h_exec with
    | dynCom _ _ _ h_body_exec =>
      -- Exec Γ (f s) s (.normal s')
      exact h_ok s' h_body_exec
  · intro s' h_exec
    cases h_exec with
    | dynCom _ _ _ h_body_exec =>
      exact h_err s' h_body_exec
  · intro h_exec
    cases h_exec with
    | dynCom _ _ _ h_body_exec =>
      exact h_fault h_body_exec

/-! ## L1corres_while

The while proof requires induction on the Exec derivation. We use a generalized
helper that does induction with a command-equation hypothesis, since the command
index (.while b c) is not a variable.
-/

/-- Helper: if L1.while doesn't fail, then the body doesn't fail when
    the condition is true. -/
private theorem L1_while_body_not_failed {σ : Type} {b : σ → Bool}
    {m : L1Monad σ}
    {s : σ} (h_nf : ¬(L1.while b m s).failed) (hb : b s = true) :
    ¬(m s).failed := by
  intro hf; apply h_nf
  simp only [L1.while]
  exact L1.WhileFail.here s hb hf

/-- Helper: if L1.while doesn't fail and the body produces an ok-result
    at some s', then L1.while doesn't fail at s' either. -/
private theorem L1_while_step_not_failed {σ : Type} {b : σ → Bool}
    {m : L1Monad σ}
    {s s' : σ} (h_nf : ¬(L1.while b m s).failed) (hb : b s = true)
    (h_body : (Except.ok (), s') ∈ (m s).results) :
    ¬(L1.while b m s').failed := by
  intro hf; apply h_nf
  simp only [L1.while] at hf ⊢
  exact L1.WhileFail.later s s' hb h_body hf

/-- Generalized while helper: for any Exec derivation `Exec Γ cmd s out`
    where `cmd = .while b c` and L1corres holds for body, construct the
    L1.WhileResult / show no fault. Generalizing `cmd` allows induction. -/
private theorem L1corres_while_aux {σ : Type} (Γ : ProcEnv σ) {b : σ → Bool}
    {m : L1Monad σ} {c : CSimpl σ}
    (hm : L1corres Γ m c)
    (cmd : CSimpl σ) (s : σ) (out : Outcome σ)
    (h_exec : Exec Γ cmd s out) (h_eq : cmd = .while b c)
    (h_nf : ¬(L1.while b m s).failed) :
    (∀ s', out = .normal s' → L1.WhileResult b m s (Except.ok (), s')) ∧
    (∀ s', out = .abrupt s' → L1.WhileResult b m s (Except.error (), s')) ∧
    (out ≠ .fault) := by
  induction h_exec with
  | skip => cases h_eq
  | basic => cases h_eq
  | seqNormal => cases h_eq
  | seqAbrupt => cases h_eq
  | seqFault => cases h_eq
  | condTrue => cases h_eq
  | condFalse => cases h_eq
  | callDefined => cases h_eq
  | callUndefined => cases h_eq
  | guardOk => cases h_eq
  | guardFault => cases h_eq
  | throw => cases h_eq
  | catchNormal => cases h_eq
  | catchAbrupt => cases h_eq
  | catchFault => cases h_eq
  | specNormal => cases h_eq
  | specStuck => cases h_eq
  | dynCom => cases h_eq
  | whileFalse b' c' s₀ hb =>
    obtain ⟨rfl, rfl⟩ := CSimpl.while.inj h_eq
    refine ⟨?_, ?_, ?_⟩
    · intro s' h; cases h; exact L1.WhileResult.done s₀ hb
    · intro s' h; cases h
    · intro h; cases h
  | whileTrue b' c' s₀ t u hb h_body_exec h_loop_exec ih_body ih_loop =>
    obtain ⟨rfl, rfl⟩ := CSimpl.while.inj h_eq
    have h_nf_body := L1_while_body_not_failed h_nf hb
    obtain ⟨hm_ok, _, _⟩ := hm s₀ h_nf_body
    have h_m_t := hm_ok t h_body_exec
    have h_nf_loop := L1_while_step_not_failed h_nf hb h_m_t
    obtain ⟨ih_ok, ih_err, ih_no_fault⟩ := ih_loop rfl h_nf_loop
    refine ⟨?_, ?_, ?_⟩
    · intro s' h; exact L1.WhileResult.step s₀ t _ hb h_m_t (ih_ok s' h)
    · intro s' h; exact L1.WhileResult.step s₀ t _ hb h_m_t (ih_err s' h)
    · intro h; exact ih_no_fault h
  | whileAbrupt b' c' s₀ t hb h_body_exec =>
    obtain ⟨rfl, rfl⟩ := CSimpl.while.inj h_eq
    have h_nf_body := L1_while_body_not_failed h_nf hb
    obtain ⟨_, hm_err, _⟩ := hm s₀ h_nf_body
    have h_m_t := hm_err t h_body_exec
    refine ⟨?_, ?_, ?_⟩
    · intro s' h; cases h
    · intro s' h; cases h; exact L1.WhileResult.abrupt s₀ t hb h_m_t
    · intro h; cases h
  | whileFault b' c' s₀ hb h_body_fault =>
    obtain ⟨rfl, rfl⟩ := CSimpl.while.inj h_eq
    have h_nf_body := L1_while_body_not_failed h_nf hb
    obtain ⟨_, _, hm_fault⟩ := hm s₀ h_nf_body
    exact absurd h_body_fault hm_fault

theorem L1corres_while {σ : Type} (Γ : ProcEnv σ) {b : σ → Bool}
    {m : L1Monad σ} {c : CSimpl σ}
    (hm : L1corres Γ m c) :
    L1corres Γ (L1.while b m) (.while b c) := by
  intro s h_nf
  refine ⟨?_, ?_, ?_⟩
  · intro s' h_exec
    simp only [L1.while]
    exact (L1corres_while_aux Γ hm _ _ _ h_exec rfl h_nf).1 s' rfl
  · intro s' h_exec
    simp only [L1.while]
    exact (L1corres_while_aux Γ hm _ _ _ h_exec rfl h_nf).2.1 s' rfl
  · intro h_exec
    exact (L1corres_while_aux Γ hm _ _ _ h_exec rfl h_nf).2.2 rfl

/-! # Phase 1: manual L1 conversion for gcd

All L1corres lemmas (skip, basic, throw, seq, cond, catch, guard, while)
are fully proved as theorems. No axioms remain. The proofs rely on:
- Set membership reasoning for seq/catch result sets
- Case analysis on Exec derivations for cond/guard
- Generalized induction on Exec (with command-equation) for while

For Phase 1, we manually construct L1 versions and compose the lemmas.
The MetaM automation (Phase 2) will generate these compositions automatically. -/

/-! # Bridge: L1corres + validHoare -> cHoare

This theorem connects the L1 monadic world to the CSimpl Exec world.
If the L1 monad overapproximates the CSimpl Exec semantics (L1corres),
and the L1 monad satisfies a Hoare triple, then the CSimpl program
satisfies a corresponding Hoare triple. -/

theorem L1corres_cHoare_bridge {σ : Type} {Γ : ProcEnv σ}
    {m : L1Monad σ} {c : CSimpl σ}
    (h_corres : L1corres Γ m c)
    {P : σ → Prop}
    {Q_ok : σ → Prop}
    {Q_err : σ → Prop}
    (h_hoare : validHoare P m (fun r s =>
      match r with
      | Except.ok () => Q_ok s
      | Except.error () => Q_err s)) :
    cHoare Γ P c Q_ok Q_err := by
  intro s h_P o h_exec
  have ⟨h_nf, h_post⟩ := h_hoare s h_P
  obtain ⟨h_ok, h_err, h_no_fault⟩ := h_corres s h_nf
  match o with
  | .normal s' =>
    have h_mem := h_ok s' h_exec
    exact h_post (Except.ok ()) s' h_mem
  | .abrupt s' =>
    have h_mem := h_err s' h_exec
    exact h_post (Except.error ()) s' h_mem
  | .fault =>
    exact absurd h_exec h_no_fault
