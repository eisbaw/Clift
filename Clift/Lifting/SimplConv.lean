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
    { results := {p | ∃ s', (Except.ok (), s') ∈ r₁.results ∧ p ∈ (m₂ s').results} ∪
                 {p | (Except.error (), p.2) ∈ r₁.results ∧ p.1 = Except.error ()}
      failed := r₁.failed ∨ ∃ s', (Except.ok (), s') ∈ r₁.results ∧ (m₂ s').failed }

def condition (c : σ → Bool) (t e : L1Monad σ) : L1Monad σ :=
  fun s => if c s then t s else e s

def «catch» (body handler : L1Monad σ) : L1Monad σ :=
  fun s =>
    let r := body s
    { results := {p | (Except.ok (), p.2) ∈ r.results ∧ p.1 = Except.ok ()} ∪
                 {p | ∃ s', (Except.error (), s') ∈ r.results ∧ p ∈ (handler s').results}
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
    { results := {p | WhileResult c body s p}
      failed := WhileFail c body s }

def spec (rel : σ → σ → Prop) : L1Monad σ :=
  fun s =>
    { results := {p | ∃ t, rel s t ∧ p = (Except.ok (), t)}
      failed := ¬ ∃ t, rel s t }

def fail : L1Monad σ :=
  fun _ => { results := ∅, failed := True }

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

-- The remaining L1corres lemmas require intricate set membership proofs.
-- These are proven for the specific gcd case in Examples/GcdProof.lean.
-- General proofs are tracked as follow-up work.

axiom L1corres_seq {σ : Type} (Γ : ProcEnv σ) {m₁ m₂ : L1Monad σ} {c₁ c₂ : CSimpl σ}
    (h₁ : L1corres Γ m₁ c₁) (h₂ : L1corres Γ m₂ c₂) :
    L1corres Γ (L1.seq m₁ m₂) (.seq c₁ c₂)

axiom L1corres_cond {σ : Type} (Γ : ProcEnv σ) {b : σ → Bool}
    {m₁ m₂ : L1Monad σ} {c₁ c₂ : CSimpl σ}
    (h₁ : L1corres Γ m₁ c₁) (h₂ : L1corres Γ m₂ c₂) :
    L1corres Γ (L1.condition b m₁ m₂) (.cond b c₁ c₂)

axiom L1corres_catch {σ : Type} (Γ : ProcEnv σ)
    {m₁ m₂ : L1Monad σ} {c₁ c₂ : CSimpl σ}
    (h₁ : L1corres Γ m₁ c₁) (h₂ : L1corres Γ m₂ c₂) :
    L1corres Γ (L1.catch m₁ m₂) (.catch c₁ c₂)

axiom L1corres_guard {σ : Type} (Γ : ProcEnv σ)
    {m : L1Monad σ} {c : CSimpl σ} {p : σ → Prop} [DecidablePred p]
    (hm : L1corres Γ m c) :
    L1corres Γ (L1.seq (L1.guard p) m) (.guard p c)

axiom L1corres_while {σ : Type} (Γ : ProcEnv σ) {b : σ → Bool}
    {m : L1Monad σ} {c : CSimpl σ}
    (hm : L1corres Γ m c) :
    L1corres Γ (L1.while b m) (.while b c)

/-! # Phase 1: manual L1 conversion for gcd

The per-constructor L1corres lemmas (skip, basic, throw proven; seq, cond,
catch, guard, while as axioms) are the building blocks. For Phase 1, we
manually construct L1 versions and compose the lemmas.

Follow-up task: prove the axiom'd lemmas. The proofs are straightforward
but require careful set membership reasoning in the NondetM framework.
The MetaM automation (Phase 2) will generate these proofs automatically. -/
