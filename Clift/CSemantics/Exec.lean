-- Big-step inductive execution semantics for CSimpl
-- Following Simpl: non-termination = no derivation (partial correctness)
--
-- This is an inductive Prop (NOT computable). You cannot #eval an Exec derivation.
-- Testing uses the CImporter's test suite against the C compiler, not Lean evaluation.
--
-- The semantics define a least fixed point: a program either terminates
-- with a derivation or diverges (no derivation exists). This naturally
-- gives partial correctness.
--
-- Reference: plan.md Decision 5
-- Reference: Simpl Semantic.thy

import Clift.CSemantics.Outcome
import Clift.CSemantics.CSimpl
import Clift.CSemantics.ProcEnv

/-! # Big-step inductive execution semantics -/

/-- Big-step execution relation for CSimpl commands.

    `Exec Γ c s o` means: in procedure environment Γ, executing command c
    starting in state s, the execution terminates with outcome o.

    If execution does not terminate (e.g., infinite while loop), there is
    simply no derivation of `Exec Γ c s o` for any o. This is the standard
    treatment in Simpl — partial correctness comes for free.

    Rules for all 11 CSimpl constructors: -/
inductive Exec {σ : Type} (Γ : ProcEnv σ) : CSimpl σ → σ → Outcome σ → Prop where
  -- skip: no-op, returns normally with unchanged state
  | skip (s : σ) :
      Exec Γ .skip s (.normal s)

  -- basic: apply state transformation, return normally
  | basic (f : σ → σ) (s : σ) :
      Exec Γ (.basic f) s (.normal (f s))

  -- seq: sequential composition, first command completes normally
  | seqNormal (c₁ c₂ : CSimpl σ) (s : σ) (t : σ) (u : Outcome σ) :
      Exec Γ c₁ s (.normal t) →
      Exec Γ c₂ t u →
      Exec Γ (.seq c₁ c₂) s u

  -- seq: first command exits abruptly, skip second command
  | seqAbrupt (c₁ c₂ : CSimpl σ) (s : σ) (t : σ) :
      Exec Γ c₁ s (.abrupt t) →
      Exec Γ (.seq c₁ c₂) s (.abrupt t)

  -- seq: first command faults, skip second command
  | seqFault (c₁ c₂ : CSimpl σ) (s : σ) :
      Exec Γ c₁ s .fault →
      Exec Γ (.seq c₁ c₂) s .fault

  -- cond: condition true, execute true branch
  | condTrue (b : σ → Bool) (c₁ c₂ : CSimpl σ) (s : σ) (t : Outcome σ) :
      b s = true →
      Exec Γ c₁ s t →
      Exec Γ (.cond b c₁ c₂) s t

  -- cond: condition false, execute false branch
  | condFalse (b : σ → Bool) (c₁ c₂ : CSimpl σ) (s : σ) (t : Outcome σ) :
      b s = false →
      Exec Γ c₂ s t →
      Exec Γ (.cond b c₁ c₂) s t

  -- while: condition true, execute body (normal), continue loop
  | whileTrue (b : σ → Bool) (c : CSimpl σ) (s t : σ) (u : Outcome σ) :
      b s = true →
      Exec Γ c s (.normal t) →
      Exec Γ (.while b c) t u →
      Exec Γ (.while b c) s u

  -- while: condition false, exit loop normally
  | whileFalse (b : σ → Bool) (c : CSimpl σ) (s : σ) :
      b s = false →
      Exec Γ (.while b c) s (.normal s)

  -- while: condition true, body exits abruptly, propagate
  | whileAbrupt (b : σ → Bool) (c : CSimpl σ) (s t : σ) :
      b s = true →
      Exec Γ c s (.abrupt t) →
      Exec Γ (.while b c) s (.abrupt t)

  -- while: condition true, body faults, propagate
  | whileFault (b : σ → Bool) (c : CSimpl σ) (s : σ) :
      b s = true →
      Exec Γ c s .fault →
      Exec Γ (.while b c) s .fault

  -- call: procedure found, execute body
  | callDefined (p : ProcName) (body : CSimpl σ) (s : σ) (t : Outcome σ) :
      Γ p = some body →
      Exec Γ body s t →
      Exec Γ (.call p) s t

  -- call: procedure not found, fault
  | callUndefined (p : ProcName) (s : σ) :
      Γ p = none →
      Exec Γ (.call p) s .fault

  -- guard: predicate holds, execute body
  | guardOk (pred : σ → Prop) (c : CSimpl σ) (s : σ) (t : Outcome σ) :
      pred s →
      Exec Γ c s t →
      Exec Γ (.guard pred c) s t

  -- guard: predicate fails, fault (undefined behavior)
  | guardFault (pred : σ → Prop) (c : CSimpl σ) (s : σ) :
      ¬ pred s →
      Exec Γ (.guard pred c) s .fault

  -- throw: produce abrupt outcome
  | throw (s : σ) :
      Exec Γ .throw s (.abrupt s)

  -- catch: body completes normally, pass through
  | catchNormal (c₁ c₂ : CSimpl σ) (s : σ) (t : σ) :
      Exec Γ c₁ s (.normal t) →
      Exec Γ (.catch c₁ c₂) s (.normal t)

  -- catch: body exits abruptly, run handler
  | catchAbrupt (c₁ c₂ : CSimpl σ) (s t : σ) (u : Outcome σ) :
      Exec Γ c₁ s (.abrupt t) →
      Exec Γ c₂ t u →
      Exec Γ (.catch c₁ c₂) s u

  -- catch: body faults, propagate (faults are not catchable)
  | catchFault (c₁ c₂ : CSimpl σ) (s : σ) :
      Exec Γ c₁ s .fault →
      Exec Γ (.catch c₁ c₂) s .fault

  -- spec: nondeterministic specification, related state exists
  | specNormal (rel : σ → σ → Prop) (s t : σ) :
      rel s t →
      Exec Γ (.spec rel) s (.normal t)

  -- spec: no related state exists, fault (stuck)
  | specStuck (rel : σ → σ → Prop) (s : σ) :
      (∀ t, ¬ rel s t) →
      Exec Γ (.spec rel) s .fault

  -- dynCom: evaluate state-dependent command, then execute it
  | dynCom (f : σ → CSimpl σ) (s : σ) (t : Outcome σ) :
      Exec Γ (f s) s t →
      Exec Γ (.dynCom f) s t

/-! # Termination predicate -/

/-- Termination predicate for CSimpl commands.

    `Terminates Γ c s` means: execution of command c in state s
    under procedure environment Γ terminates (i.e., there exists
    some outcome o such that `Exec Γ c s o`).

    This is a separate inductive predicate following Simpl's `terminates`.
    Total correctness = partial correctness + termination.

    The inductive structure mirrors Exec but tracks what is needed
    for termination rather than computing the outcome. For while loops,
    termination requires that the body terminates AND the recursive
    invocation terminates. -/
inductive Terminates {σ : Type} (Γ : ProcEnv σ) : CSimpl σ → σ → Prop where
  -- skip and basic always terminate
  | skip (s : σ) :
      Terminates Γ .skip s

  | basic (f : σ → σ) (s : σ) :
      Terminates Γ (.basic f) s

  -- seq: first command terminates, and for every normal outcome,
  -- the second command terminates in the resulting state
  | seq (c₁ c₂ : CSimpl σ) (s : σ) :
      Terminates Γ c₁ s →
      (∀ t, Exec Γ c₁ s (.normal t) → Terminates Γ c₂ t) →
      Terminates Γ (.seq c₁ c₂) s

  -- cond: the chosen branch terminates
  | condTrue (b : σ → Bool) (c₁ c₂ : CSimpl σ) (s : σ) :
      b s = true →
      Terminates Γ c₁ s →
      Terminates Γ (.cond b c₁ c₂) s

  | condFalse (b : σ → Bool) (c₁ c₂ : CSimpl σ) (s : σ) :
      b s = false →
      Terminates Γ c₂ s →
      Terminates Γ (.cond b c₁ c₂) s

  -- while: if condition false, trivially terminates.
  -- If condition true, body terminates AND for every normal outcome
  -- of the body, the loop terminates from the resulting state.
  | whileFalse (b : σ → Bool) (c : CSimpl σ) (s : σ) :
      b s = false →
      Terminates Γ (.while b c) s

  | whileTrue (b : σ → Bool) (c : CSimpl σ) (s : σ) :
      b s = true →
      Terminates Γ c s →
      (∀ t, Exec Γ c s (.normal t) → Terminates Γ (.while b c) t) →
      Terminates Γ (.while b c) s

  -- call: if procedure found, body terminates
  | callDefined (p : ProcName) (body : CSimpl σ) (s : σ) :
      Γ p = some body →
      Terminates Γ body s →
      Terminates Γ (.call p) s

  | callUndefined (p : ProcName) (s : σ) :
      Γ p = none →
      Terminates Γ (.call p) s

  -- guard: if predicate holds, body terminates. If not, trivially terminates (faults).
  | guardOk (pred : σ → Prop) (c : CSimpl σ) (s : σ) :
      pred s →
      Terminates Γ c s →
      Terminates Γ (.guard pred c) s

  | guardFault (pred : σ → Prop) (c : CSimpl σ) (s : σ) :
      ¬ pred s →
      Terminates Γ (.guard pred c) s

  -- throw always terminates
  | throw (s : σ) :
      Terminates Γ .throw s

  -- catch: body terminates, and for every abrupt outcome, handler terminates
  | catch (c₁ c₂ : CSimpl σ) (s : σ) :
      Terminates Γ c₁ s →
      (∀ t, Exec Γ c₁ s (.abrupt t) → Terminates Γ c₂ t) →
      Terminates Γ (.catch c₁ c₂) s

  -- spec always terminates (either produces a state or faults)
  | spec (rel : σ → σ → Prop) (s : σ) :
      Terminates Γ (.spec rel) s

  -- dynCom: the chosen command terminates
  | dynCom (f : σ → CSimpl σ) (s : σ) :
      Terminates Γ (f s) s →
      Terminates Γ (.dynCom f) s
