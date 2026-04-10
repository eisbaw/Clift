-- L2 Rewrite: genuine local variable extraction (CState -> Globals)
--
-- Unlike l2_wrap which wraps an L1 computation, this module defines
-- the L2 rewrite correspondence where the state type is Globals only
-- and locals are threaded as explicit input/output parameters.
--
-- After L2 rewrite, the computation has type:
--   Locals → NondetM Globals (Except Unit Unit × Locals)
-- The state is Globals only. Locals are input/output explicitly.
--
-- Reference: ext/AutoCorres2/LocalVarExtract.thy

import Clift.Lifting.SimplConv
import Clift.Lifting.LocalVarExtract

set_option maxHeartbeats 3200000

/-! # L2 rewritten computation type -/

/-- An L2 computation: Globals-only state, locals threaded explicitly.
    Takes initial locals, returns (result, final locals) in Globals state monad. -/
abbrev L2Monad (Locals : Type) := Locals → NondetM Globals (Except Unit Unit × Locals)

/-! # L2corres_rw: correspondence between rewritten L2 and L1

    For every CState s₁ = ⟨g, locs⟩, running the L1 computation on s₁
    corresponds to running the L2 computation with locs on g. -/
def L2corres_rw {Locals : Type}
    (m2 : L2Monad Locals)
    (m1 : L1Monad (CState Locals)) : Prop :=
  ∀ (g : Globals) (locs : Locals),
    let s := CState.mk g locs
    -- Failure agreement
    ((m2 locs g).failed ↔ (m1 s).failed) ∧
    -- Forward: L1 result -> L2 result
    (∀ r g' locs', (r, CState.mk g' locs') ∈ (m1 s).results →
      ((r, locs'), g') ∈ (m2 locs g).results) ∧
    -- Backward: L2 result -> L1 result
    (∀ r locs' g', ((r, locs'), g') ∈ (m2 locs g).results →
      (r, CState.mk g' locs') ∈ (m1 s).results)

/-! # L2 combinators -/

namespace L2rw

variable {Locals : Type}

def skip : L2Monad Locals :=
  fun locs => NondetM.pure (Except.ok (), locs)

def throw : L2Monad Locals :=
  fun locs => NondetM.pure (Except.error (), locs)

def modifyLocals (f : Locals → Locals) : L2Monad Locals :=
  fun locs => NondetM.pure (Except.ok (), f locs)

def modify (fg : Globals → Locals → Globals) (fl : Globals → Locals → Locals) : L2Monad Locals :=
  fun locs => fun g => { results := {((Except.ok (), fl g locs), fg g locs)}, failed := False }

def guard (p : Globals → Locals → Prop) [∀ g l, Decidable (p g l)] : L2Monad Locals :=
  fun locs => fun g =>
    if p g locs
    then { results := {((Except.ok (), locs), g)}, failed := False }
    else { results := ∅, failed := True }

end L2rw

/-! # L2corres_rw combinator lemmas -/

-- Helper: membership in singleton set
private theorem mem_singleton_pair {α β : Type} {a a' : α} {b b' : β}
    (ha : a' = a) (hb : b' = b) : (a', b') ∈ ({(a, b)} : Set (α × β)) :=
  Set.mem_singleton_iff.mpr (by rw [ha, hb])

theorem L2corres_rw_skip {Locals : Type} :
    L2corres_rw (L2rw.skip : L2Monad Locals) (L1.skip : L1Monad (CState Locals)) := by
  intro g locs
  unfold L2rw.skip L1.skip NondetM.pure
  refine ⟨⟨fun h => h, fun h => h⟩, ?_, ?_⟩
  · intro r g' locs' h
    have heq := Set.mem_singleton_iff.mp h
    have : r = Except.ok () := congrArg Prod.fst heq
    have : CState.mk g' locs' = CState.mk g locs := congrArg Prod.snd heq
    have hg : g' = g := congrArg CState.globals this
    have hl : locs' = locs := congrArg CState.locals this
    exact mem_singleton_pair (by rw [‹r = _›, hl]) hg
  · intro r locs' g' h
    have heq := Set.mem_singleton_iff.mp h
    have hr : (r, locs') = (Except.ok (), locs) := congrArg Prod.fst heq
    have hg : g' = g := congrArg Prod.snd heq
    have : r = Except.ok () := congrArg Prod.fst hr
    have : locs' = locs := congrArg Prod.snd hr
    exact mem_singleton_pair (by rw [‹r = _›]) (by rw [hg, ‹locs' = _›])

theorem L2corres_rw_throw {Locals : Type} :
    L2corres_rw (L2rw.throw : L2Monad Locals) (L1.throw : L1Monad (CState Locals)) := by
  intro g locs
  unfold L2rw.throw L1.throw NondetM.pure
  refine ⟨⟨fun h => h, fun h => h⟩, ?_, ?_⟩
  · intro r g' locs' h
    have heq := Set.mem_singleton_iff.mp h
    have : r = Except.error () := congrArg Prod.fst heq
    have : CState.mk g' locs' = CState.mk g locs := congrArg Prod.snd heq
    have hg : g' = g := congrArg CState.globals this
    have hl : locs' = locs := congrArg CState.locals this
    exact mem_singleton_pair (by rw [‹r = Except.error ()›, hl]) hg
  · intro r locs' g' h
    have heq := Set.mem_singleton_iff.mp h
    have hr : (r, locs') = (Except.error (), locs) := congrArg Prod.fst heq
    have hg : g' = g := congrArg Prod.snd heq
    have : r = Except.error () := congrArg Prod.fst hr
    have : locs' = locs := congrArg Prod.snd hr
    exact mem_singleton_pair (by rw [‹r = _›]) (by rw [hg, ‹locs' = _›])

/-- L2corres_rw for modify that only touches locals. -/
theorem L2corres_rw_modifyLocals {Locals : Type}
    (fl : Locals → Locals)
    (f1 : CState Locals → CState Locals)
    (h_eq : ∀ g locs, f1 ⟨g, locs⟩ = ⟨g, fl locs⟩) :
    L2corres_rw (L2rw.modifyLocals fl) (L1.modify f1) := by
  intro g locs
  unfold L2rw.modifyLocals L1.modify NondetM.pure
  refine ⟨⟨fun h => h, fun h => h⟩, ?_, ?_⟩
  · intro r g' locs' h
    have heq := Set.mem_singleton_iff.mp h
    have : r = Except.ok () := congrArg Prod.fst heq
    have : CState.mk g' locs' = f1 ⟨g, locs⟩ := congrArg Prod.snd heq
    rw [h_eq] at this
    have hg : g' = g := congrArg CState.globals this
    have hl : locs' = fl locs := congrArg CState.locals this
    exact mem_singleton_pair (by rw [‹r = _›, hl]) hg
  · intro r locs' g' h
    have heq := Set.mem_singleton_iff.mp h
    have hr : (r, locs') = (Except.ok (), fl locs) := congrArg Prod.fst heq
    have hg : g' = g := congrArg Prod.snd heq
    have : r = Except.ok () := congrArg Prod.fst hr
    have : locs' = fl locs := congrArg Prod.snd hr
    rw [h_eq]; exact mem_singleton_pair (by rw [‹r = _›]) (by rw [hg, ‹locs' = _›])

/-- L2corres_rw for modify that touches both globals and locals. -/
theorem L2corres_rw_modify {Locals : Type}
    (fg : Globals → Locals → Globals)
    (fl : Globals → Locals → Locals)
    (f1 : CState Locals → CState Locals)
    (h_eq : ∀ g locs, f1 ⟨g, locs⟩ = ⟨fg g locs, fl g locs⟩) :
    L2corres_rw (L2rw.modify fg fl) (L1.modify f1) := by
  intro g locs
  unfold L2rw.modify L1.modify
  refine ⟨⟨fun h => h, fun h => h⟩, ?_, ?_⟩
  · intro r g' locs' h
    have heq := Set.mem_singleton_iff.mp h
    have : r = Except.ok () := congrArg Prod.fst heq
    have : CState.mk g' locs' = f1 ⟨g, locs⟩ := congrArg Prod.snd heq
    rw [h_eq] at this
    have hg : g' = fg g locs := congrArg CState.globals this
    have hl : locs' = fl g locs := congrArg CState.locals this
    exact mem_singleton_pair (by rw [‹r = _›, hl]) hg
  · intro r locs' g' h
    have heq := Set.mem_singleton_iff.mp h
    have hr : (r, locs') = (Except.ok (), fl g locs) := congrArg Prod.fst heq
    have hg : g' = fg g locs := congrArg Prod.snd heq
    have : r = Except.ok () := congrArg Prod.fst hr
    have : locs' = fl g locs := congrArg Prod.snd hr
    rw [h_eq]; exact mem_singleton_pair (by rw [‹r = _›]) (by rw [hg, ‹locs' = _›])

/-- L2corres_rw for guard. -/
theorem L2corres_rw_guard {Locals : Type}
    (p2 : Globals → Locals → Prop) [∀ g l, Decidable (p2 g l)]
    (p1 : CState Locals → Prop) [DecidablePred p1]
    (h_eq : ∀ g locs, p2 g locs ↔ p1 ⟨g, locs⟩) :
    L2corres_rw (L2rw.guard p2) (L1.guard p1) := by
  intro g locs
  unfold L2rw.guard L1.guard
  have h_iff := h_eq g locs
  by_cases hp : p2 g locs
  · -- Guard holds: both produce singleton ok results
    have hp1 : p1 ⟨g, locs⟩ := h_iff.mp hp
    simp only [if_pos hp, if_pos hp1]
    constructor
    · trivial
    constructor
    · intro r g' locs' h
      have heq := Set.mem_singleton_iff.mp h
      have : r = Except.ok () := congrArg Prod.fst heq
      have : CState.mk g' locs' = CState.mk g locs := congrArg Prod.snd heq
      have hg : g' = g := congrArg CState.globals this
      have hl : locs' = locs := congrArg CState.locals this
      exact mem_singleton_pair (by rw [‹r = _›, hl]) hg
    · intro r locs' g' h
      have heq := Set.mem_singleton_iff.mp h
      have hr : (r, locs') = (Except.ok (), locs) := congrArg Prod.fst heq
      have hg : g' = g := congrArg Prod.snd heq
      have : r = Except.ok () := congrArg Prod.fst hr
      have : locs' = locs := congrArg Prod.snd hr
      exact mem_singleton_pair (by rw [‹r = _›]) (by rw [hg, ‹locs' = _›])
  · -- Guard fails: both fail
    have hp1 : ¬p1 ⟨g, locs⟩ := mt h_iff.mpr hp
    simp only [if_neg hp, if_neg hp1]
    refine ⟨?_, fun _ _ _ h => absurd h (Set.not_mem_empty _),
              fun _ _ _ h => absurd h (Set.not_mem_empty _)⟩
    trivial

/-! # Hoare transfer for L2 rewrite -/

/-- Transfer validHoare from L2 rewrite to L1. -/
theorem L2corres_rw_validHoare {Locals : Type}
    {m2 : L2Monad Locals} {m1 : L1Monad (CState Locals)}
    (hcorres : L2corres_rw m2 m1)
    {P : Globals → Locals → Prop}
    {Q : Except Unit Unit → Locals → Globals → Prop}
    (h2 : ∀ g locs, P g locs →
      ¬(m2 locs g).failed ∧
      ∀ r locs' g', ((r, locs'), g') ∈ (m2 locs g).results → Q r locs' g') :
    validHoare
      (fun s : CState Locals => P s.globals s.locals)
      m1
      (fun r s' => Q r s'.locals s'.globals) := by
  intro s hP
  obtain ⟨h_fail, h_fwd, _⟩ := hcorres s.globals s.locals
  obtain ⟨h2_nf, h2_post⟩ := h2 s.globals s.locals hP
  constructor
  · intro hf; exact h2_nf (h_fail.mpr hf)
  · intro r s' h_mem
    -- s' : CState Locals, decompose it
    have h_l2_mem := h_fwd r s'.globals s'.locals h_mem
    exact h2_post r s'.locals s'.globals h_l2_mem

/-! # Summary

L2 rewrite defines genuine local variable extraction:
- State type is Globals only (no Locals record in state)
- Locals are threaded as explicit input/output parameters
- L2corres_rw relates rewritten L2 to L1 via bidirectional simulation
- Combinator lemmas enable compositional proofs

Key types:
- L2Monad Locals := Locals → NondetM Globals (Except Unit Unit × Locals)

Key definitions:
- L2rw.skip, throw, modifyLocals, modify, guard
- L2corres_rw: the correspondence relation
- L2corres_rw_skip, _throw, _modifyLocals, _modify, _guard: combinator lemmas
- L2corres_rw_validHoare: transfer Hoare triples from L2 to L1
-/
