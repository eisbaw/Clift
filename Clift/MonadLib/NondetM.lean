-- NondetM: Nondeterministic state monad with failure
-- Foundation for all C verification in Clift
--
-- Design: follows seL4's nondet_monad structure.
-- NondetM.run : σ → { results : Set (α × σ), failed : Prop }
-- The failure flag is Prop (not Bool) because we never evaluate this monad;
-- we only reason about it in proofs.
--
-- Reference: ext/AutoCorres2/lib/Spec_Monad.thy, ext/AutoCorres2/L1Defs.thy

import Mathlib.Data.Set.Basic

/-! # Error types for C verification -/

/-- Kinds of errors that C programs can produce.
    These are used to classify failures in the verification pipeline. -/
inductive CError where
  | undefinedBehavior : CError
  | overflow          : CError
  | nullDeref         : CError
  deriving DecidableEq, Repr

/-- Result type for C computations: either a value or an error. -/
inductive CResult (α : Type) where
  | ok   : α → CResult α
  | fail : CError → CResult α
  deriving Repr

/-! # NondetM: Nondeterministic state monad with failure -/

/-- The outcome of running a nondeterministic computation on a state.
    - `results`: the set of all possible (return_value, final_state) pairs
    - `failed`: whether failure is a possible outcome

    This is NOT computable. We never `#eval` this; we reason about it in proofs. -/
structure NondetResult (σ α : Type) where
  results : Set (α × σ)
  failed  : Prop

/-- Nondeterministic state monad with failure.
    The core monad for all C verification in Clift.

    Morally: `NondetM σ α ≈ σ → { results : Set (α × σ), failed : Prop }`

    Following seL4's `nondet_monad` / `spec_monad`:
    - Results are a *set* of (value, state) pairs (nondeterminism)
    - A separate failure flag tracks whether failure is possible
    - Bind unions results from all continuations
    - Failure propagates: if the first computation can fail, or if any
      continuation from a successful result can fail, the composed
      computation can fail -/
def NondetM (σ α : Type) := σ → NondetResult σ α

namespace NondetM

variable {σ α β γ : Type}

/-! ## Core monad operations -/

/-- Pure: return a value without changing state or failing. -/
def pure (a : α) : NondetM σ α :=
  fun s => { results := {(a, s)}, failed := False }

/-- Bind: sequence two computations. Run `m`, then for each successful
    result `(a, s')`, run `f a` in state `s'`. Union all results.
    Failure propagates from either `m` or any continuation. -/
def bind (m : NondetM σ α) (f : α → NondetM σ β) : NondetM σ β :=
  fun s =>
    let r := m s
    { results := {p : β × σ | ∃ a s', (a, s') ∈ r.results ∧ p ∈ (f a s').results}
      failed  := r.failed ∨ ∃ a s', (a, s') ∈ r.results ∧ (f a s').failed }

/-- Fail: computation that always fails with no successful results. -/
def fail : NondetM σ α :=
  fun _ => { results := ∅, failed := True }

/-- Get: return the current state. -/
def get : NondetM σ σ :=
  fun s => { results := {(s, s)}, failed := False }

/-- Put: replace the state. -/
def put (s : σ) : NondetM σ Unit :=
  fun _ => { results := {((), s)}, failed := False }

/-- Modify: apply a function to the state. -/
def modify (f : σ → σ) : NondetM σ Unit :=
  fun s => { results := {((), f s)}, failed := False }

/-- Guard: fail if the predicate does not hold, otherwise skip.
    Models C undefined behavior guards. -/
def guard (p : σ → Prop) [DecidablePred p] : NondetM σ Unit :=
  fun s => if p s then { results := {((), s)}, failed := False }
           else { results := ∅, failed := True }

/-- Select: nondeterministically choose a value from a set.
    Never fails (even on empty set -- just produces no results). -/
def select (S : Set α) : NondetM σ α :=
  fun s => { results := {p | p.1 ∈ S ∧ p.2 = s}, failed := False }

/-- Condition: branch on a boolean predicate over state. -/
def condition (c : σ → Bool) (t e : NondetM σ α) : NondetM σ α :=
  fun s => if c s then t s else e s

/-! ## Monad instance -/

instance : Monad (NondetM σ) where
  pure := NondetM.pure
  bind := NondetM.bind

/-! ## Simp lemmas for unfolding -/

@[simp] theorem pure_run (a : α) (s : σ) :
    (Pure.pure a : NondetM σ α) s = { results := {(a, s)}, failed := False } :=
  rfl

@[simp] theorem bind_run (m : NondetM σ α) (f : α → NondetM σ β) (s : σ) :
    (m >>= f) s =
      { results := {p : β × σ | ∃ a s', (a, s') ∈ (m s).results ∧ p ∈ (f a s').results}
        failed  := (m s).failed ∨ ∃ a s', (a, s') ∈ (m s).results ∧ (f a s').failed } :=
  rfl

@[simp] theorem fail_run (s : σ) :
    (NondetM.fail : NondetM σ α) s = { results := ∅, failed := True } :=
  rfl

@[simp] theorem get_run (s : σ) :
    (NondetM.get : NondetM σ σ) s = { results := {(s, s)}, failed := False } :=
  rfl

@[simp] theorem put_run (s s' : σ) :
    (NondetM.put s : NondetM σ Unit) s' = { results := {((), s)}, failed := False } :=
  rfl

@[simp] theorem modify_run (f : σ → σ) (s : σ) :
    (NondetM.modify f : NondetM σ Unit) s = { results := {((), f s)}, failed := False } :=
  rfl

@[simp] theorem condition_run_true {c : σ → Bool} {t e : NondetM σ α} {s : σ} (h : c s = true) :
    (NondetM.condition c t e) s = t s := by
  simp [NondetM.condition, h]

@[simp] theorem condition_run_false {c : σ → Bool} {t e : NondetM σ α} {s : σ} (h : c s = false) :
    (NondetM.condition c t e) s = e s := by
  simp [NondetM.condition, h]

/-! ## NondetResult extensionality -/

@[ext] theorem NondetResult.ext {r₁ r₂ : NondetResult σ α}
    (h_results : r₁.results = r₂.results)
    (h_failed : r₁.failed ↔ r₂.failed) : r₁ = r₂ := by
  cases r₁; cases r₂
  simp only [NondetResult.mk.injEq] at *
  constructor
  · exact h_results
  · exact propext h_failed

/-- Extensionality for NondetM: two computations are equal if they produce
    the same results and failure on every state. -/
theorem ext {m₁ m₂ : NondetM σ α}
    (h : ∀ s, (m₁ s).results = (m₂ s).results ∧ ((m₁ s).failed ↔ (m₂ s).failed)) :
    m₁ = m₂ := by
  funext s
  have ⟨hr, hf⟩ := h s
  exact NondetResult.ext hr hf

/-! ## Monadic combinators matching CSimpl constructs -/

/-- Skip: no-op computation (= pure ()). -/
def skip : NondetM σ Unit := NondetM.pure ()

/-- Basic: apply a state transformation, return unit.
    This is the monadic equivalent of CSimpl.basic. -/
def basic (f : σ → σ) : NondetM σ Unit :=
  fun s => { results := {((), f s)}, failed := False }

/-- Seq: sequential composition. Just bind ignoring the first result.
    This is the monadic equivalent of CSimpl.seq. -/
def seq (m₁ : NondetM σ Unit) (m₂ : NondetM σ α) : NondetM σ α :=
  NondetM.bind m₁ (fun _ => m₂)

/-- Cond: conditional branching on a boolean predicate over state. -/
def cond (c : σ → Bool) (t e : NondetM σ α) : NondetM σ α :=
  fun s => if c s then t s else e s

/-- Inductive characterization of while loop results.
    A state s' is in the result set of `whileLoop c body` starting from s if:
    - c s = false and s' = s (zero iterations), OR
    - c s = true, body produces some intermediate state t, and s' is a
      result of whileLoop starting from t (one step + recursive) -/
inductive WhileResult (c : σ → Bool) (body : NondetM σ Unit) : σ → σ → Prop where
  | done (s : σ) (hc : c s = false) : WhileResult c body s s
  | step (s t s' : σ) (hc : c s = true)
      (h_body : ((), t) ∈ (body s).results)
      (h_rest : WhileResult c body t s') : WhileResult c body s s'

/-- Inductive characterization of while loop failure.
    The loop can fail if:
    - c s = true and body fails at s (immediate failure), OR
    - c s = true, body succeeds producing t, and the loop fails starting from t -/
inductive WhileFail (c : σ → Bool) (body : NondetM σ Unit) : σ → Prop where
  | here (s : σ) (hc : c s = true) (h_fail : (body s).failed) : WhileFail c body s
  | later (s t : σ) (hc : c s = true)
      (h_body : ((), t) ∈ (body s).results)
      (h_rest : WhileFail c body t) : WhileFail c body s

/-- While: iterate body while condition holds.
    Defined using inductive predicates for results and failure. -/
def whileLoop (c : σ → Bool) (body : NondetM σ Unit) : NondetM σ Unit :=
  fun s =>
    { results := {p : Unit × σ | WhileResult c body s p.2}
      failed := WhileFail c body s }

@[simp] theorem skip_run (s : σ) :
    (NondetM.skip : NondetM σ Unit) s = { results := {((), s)}, failed := False } :=
  rfl

@[simp] theorem basic_run (f : σ → σ) (s : σ) :
    (NondetM.basic f : NondetM σ Unit) s = { results := {((), f s)}, failed := False } :=
  rfl

-- seq_run unfolds seq into explicit form.
-- We avoid a custom simp lemma because the bind already unfolds correctly.
-- Instead, provide a theorem that users can rewrite with explicitly.
theorem seq_eq (m₁ : NondetM σ Unit) (m₂ : NondetM σ α) :
    NondetM.seq m₁ m₂ = NondetM.bind m₁ (fun _ => m₂) :=
  rfl

@[simp] theorem cond_run_true {c : σ → Bool} {t e : NondetM σ α} {s : σ} (h : c s = true) :
    (NondetM.cond c t e) s = t s := by
  simp [NondetM.cond, h]

@[simp] theorem cond_run_false {c : σ → Bool} {t e : NondetM σ α} {s : σ} (h : c s = false) :
    (NondetM.cond c t e) s = e s := by
  simp [NondetM.cond, h]

/-! ## Monad laws -/

-- Helper: membership in singleton set is just equality (definitional for Set)
private theorem mem_singleton_pair {a a' : α} {s s' : σ} :
    (a, s) ∈ ({(a', s')} : Set (α × σ)) ↔ a = a' ∧ s = s' := by
  constructor
  · intro h; exact Prod.mk.inj h
  · rintro ⟨rfl, rfl⟩; rfl

/-- Left identity: `pure a >>= f = f a` -/
theorem pure_bind (a : α) (f : α → NondetM σ β) :
    (Pure.pure a >>= f) = f a := by
  funext s
  apply NondetResult.ext
  · -- results
    ext ⟨b, s'⟩
    constructor
    · rintro ⟨a', s'', h_mem, h_in⟩
      have ⟨rfl, rfl⟩ := Prod.mk.inj h_mem
      exact h_in
    · intro h
      exact ⟨a, s, rfl, h⟩
  · -- failed
    constructor
    · rintro (h_false | ⟨a', s', h_mem, h_fail⟩)
      · exact absurd h_false id
      · have ⟨rfl, rfl⟩ := Prod.mk.inj h_mem
        exact h_fail
    · intro h
      exact Or.inr ⟨a, s, rfl, h⟩

/-- Right identity: `m >>= pure = m` -/
theorem bind_pure (m : NondetM σ α) :
    (m >>= Pure.pure) = m := by
  funext s
  apply NondetResult.ext
  · -- results
    ext ⟨a, s'⟩
    constructor
    · rintro ⟨a', s'', h_mem, h_in⟩
      have ⟨rfl, rfl⟩ := Prod.mk.inj h_in
      exact h_mem
    · intro h
      exact ⟨a, s', h, rfl⟩
  · -- failed
    constructor
    · rintro (h | ⟨a, s', _, h_fail⟩)
      · exact h
      · exact absurd h_fail id
    · intro h
      exact Or.inl h

/-- Associativity: `(m >>= f) >>= g = m >>= (fun a => f a >>= g)` -/
theorem bind_assoc (m : NondetM σ α) (f : α → NondetM σ β) (g : β → NondetM σ γ) :
    ((m >>= f) >>= g) = (m >>= fun a => f a >>= g) := by
  funext s
  apply NondetResult.ext
  · -- results
    ext ⟨c, s''⟩
    constructor
    · rintro ⟨b, s', ⟨a, s₁, h_ma, h_fb⟩, h_gc⟩
      exact ⟨a, s₁, h_ma, b, s', h_fb, h_gc⟩
    · rintro ⟨a, s₁, h_ma, b, s', h_fb, h_gc⟩
      exact ⟨b, s', ⟨a, s₁, h_ma, h_fb⟩, h_gc⟩
  · -- failed
    constructor
    · rintro (h_outer_fail | ⟨b, s', h_outer_mem, h_g_fail⟩)
      · rcases h_outer_fail with h_m_fail | ⟨a, s₁, h_ma, h_f_fail⟩
        · exact Or.inl h_m_fail
        · exact Or.inr ⟨a, s₁, h_ma, Or.inl h_f_fail⟩
      · obtain ⟨a, s₁, h_ma, h_fb⟩ := h_outer_mem
        exact Or.inr ⟨a, s₁, h_ma, Or.inr ⟨b, s', h_fb, h_g_fail⟩⟩
    · rintro (h_m_fail | ⟨a, s₁, h_ma, h_fg_fail⟩)
      · exact Or.inl (Or.inl h_m_fail)
      · rcases h_fg_fail with h_f_fail | ⟨b, s', h_fb, h_g_fail⟩
        · exact Or.inl (Or.inr ⟨a, s₁, h_ma, h_f_fail⟩)
        · exact Or.inr ⟨b, s', ⟨a, s₁, h_ma, h_fb⟩, h_g_fail⟩

end NondetM
