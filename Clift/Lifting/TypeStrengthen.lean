-- L3: TypeStrengthen — Narrow monad to tightest type (pure/option/nondet)
--
-- Following plan.md Decision 7 (3 monad levels):
--   pure (precedence 100): No state, no failure. Target: α
--   option (precedence 60): May fail, reads/writes state. Target: σ → Option (α × σ)
--   nondet (precedence 0): Full NondetM. Target: NondetM σ α
--
-- Reference: ext/AutoCorres2/TypeStrengthen.thy, ext/AutoCorres2/monad_types.ML
--
-- For Phase 2: manual/definitional approach. MetaM automation deferred.

import Clift.MonadLib

set_option maxHeartbeats 800000

/-! # Monad type hierarchy -/

/-! ## Level 1: Pure (no state, no failure)

A pure function is just a value. The injection into NondetM wraps it
as a singleton result with no failure.
-/

/-- Lift a pure value into NondetM. -/
def tsLiftPure {σ α : Type} (x : α) : NondetM σ α :=
  NondetM.pure x

@[simp] theorem tsLiftPure_run {σ α : Type} (x : α) (s : σ) :
    (tsLiftPure x : NondetM σ α) s = { results := {(x, s)}, failed := False } :=
  rfl

theorem tsLiftPure_not_failed {σ α : Type} (x : α) (s : σ) :
    ¬((tsLiftPure x : NondetM σ α) s).failed :=
  id

/-! ## Level 2: Option (may fail, reads/writes state)

An option computation is σ → Option (α × σ). It either succeeds with
a result and new state, or fails. This is deterministic and cannot be
nondeterministic.
-/

/-- Lift a deterministic-with-failure computation into NondetM.
    Some (a, s') maps to singleton result set. None maps to failure. -/
def tsLiftOption {σ α : Type} (f : σ → Option (α × σ)) : NondetM σ α :=
  fun s =>
    match f s with
    | some (a, s') => { results := {(a, s')}, failed := False }
    | none         => { results := ∅, failed := True }

@[simp] theorem tsLiftOption_run_some {σ α : Type} {f : σ → Option (α × σ)} {s : σ}
    {a : α} {s' : σ} (h : f s = some (a, s')) :
    (tsLiftOption f) s = { results := {(a, s')}, failed := False } := by
  simp [tsLiftOption, h]

@[simp] theorem tsLiftOption_run_none {σ α : Type} {f : σ → Option (α × σ)} {s : σ}
    (h : f s = none) :
    (tsLiftOption f) s = { results := ∅, failed := True } := by
  simp [tsLiftOption, h]

/-! ## L3corres: correspondence for TypeStrengthen

L3corres connects an L3 function (in a tighter monad) to a function
in NondetM. For Phase 2 we use definitional equality.
-/

/-- L3corres for pure: the NondetM computation equals tsLiftPure of a value. -/
def L3corres_pure {σ α : Type} (m : NondetM σ α) (x : α) : Prop :=
  m = tsLiftPure x

/-- L3corres for option: the NondetM computation equals tsLiftOption of a fn. -/
def L3corres_option {σ α : Type} (m : NondetM σ α) (f : σ → Option (α × σ)) : Prop :=
  m = tsLiftOption f

/-- L3corres_pure implies corres with identity relations.
    The abstract side is the pure computation (always succeeds),
    the concrete side is the original m (which must equal tsLiftPure). -/
theorem L3corres_pure_implies_corres {σ α : Type} {m : NondetM σ α} {x : α}
    (h : L3corres_pure m x) :
    corres (fun s s' => s = s') true true (fun a b => a = b)
      (fun _ => True) (fun _ => True)
      (tsLiftPure x : NondetM σ α) m := by
  unfold L3corres_pure at h; subst h
  intro s s' h_srel _ _
  subst h_srel
  refine ⟨?_, ?_, ?_⟩
  · intro _; simp [tsLiftPure, NondetM.pure]
  · intro r' t' h_mem
    have ⟨rfl, rfl⟩ := Prod.mk.inj (h_mem : (r', t') = (x, s))
    exact ⟨r', t', rfl, rfl, rfl⟩
  · intro _; simp [tsLiftPure, NondetM.pure]

/-- L3corres_option implies corres. nf=false since option can fail. -/
theorem L3corres_option_implies_corres {σ α : Type}
    {m : NondetM σ α} {f : σ → Option (α × σ)}
    (h : L3corres_option m f) :
    corres (fun s s' => s = s') false false (fun a b => a = b)
      (fun _ => True) (fun _ => True)
      (tsLiftOption f : NondetM σ α) m := by
  unfold L3corres_option at h; subst h
  intro s s' h_srel _ _
  subst h_srel
  refine ⟨fun h => Bool.noConfusion h, ?_, fun h => Bool.noConfusion h⟩
  intro r' t' h_mem
  -- m' = m = tsLiftOption f, so h_mem is about tsLiftOption f
  -- We need to find matching abstract result (which is also tsLiftOption f)
  exact ⟨r', t', h_mem, rfl, rfl⟩

/-! ## Injection tower: pure lifts into option -/

/-- A pure value can be seen as a total (never-failing) option computation. -/
def pureToOption {σ α : Type} (x : α) : σ → Option (α × σ) :=
  fun s => some (x, s)

theorem tsLiftOption_pureToOption {σ α : Type} (x : α) :
    (tsLiftOption (pureToOption x) : NondetM σ α) = tsLiftPure x := by
  funext s
  simp [tsLiftOption, pureToOption, tsLiftPure, NondetM.pure]
