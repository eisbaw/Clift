-- CSimpl: Deeply embedded imperative language for C
-- Based on Schirmer's Simpl, simplified for sequential C
--
-- All 11 constructors from plan.md Decision 4.
-- Parametric in state type σ.
--
-- Reference: plan.md Decision 4
-- Reference: Simpl Language.thy

/-! # Procedure names -/

/-- Procedure names are strings (matching the C function name). -/
abbrev ProcName := String

/-! # CSimpl: The deeply embedded imperative language -/

/-- Deeply embedded imperative language, parametric in state type σ.

    This is the target language of the CImporter (Stage 0).
    CSimpl terms represent C programs structurally.
    Execution semantics are defined by the `Exec` inductive relation.

    Constructors:
    - `skip`:    no-op
    - `basic`:   state transformation (assignments, expressions)
    - `seq`:     sequential composition
    - `cond`:    conditional branch on a decidable state predicate
    - `while`:   while loop with decidable condition
    - `call`:    procedure call by name (resolved via ProcEnv)
    - `guard`:   UB guard — faults if predicate does not hold
    - `throw`:   raise an abrupt (exception) outcome
    - `catch`:   handle abrupt outcomes from the body
    - `spec`:    nondeterministic specification (relation on states)
    - `dynCom`:  state-dependent command (used for call setup/teardown)

    Note on `guard`: the predicate is `σ → Prop` (not `σ → Bool`).
    This allows guards to express undecidable conditions in the semantics.
    In practice, generated guards from the importer will be decidable.

    Note on `guard` fault-set: Simpl's Guard takes a fault-set parameter `f`
    to classify which guard failed. Ours omits this — all faults are
    indistinguishable. This simplifies proofs and is sufficient while we
    prove total fault-freedom. See ADR-006 (backlog/docs/adr-006-guard-fault-set-deferred.md).

    Note on `spec`: models nondeterministic choice constrained by a relation.
    If no related state exists, this is equivalent to a fault.
    Used to model C operations whose result is implementation-defined.

    Note on `dynCom`: the command to execute depends on the current state.
    Used by the CImporter for procedure calls: capture current state,
    set up parameters, call body, restore caller locals. -/
inductive CSimpl (σ : Type) where
  | skip    : CSimpl σ
  | basic   : (σ → σ) → CSimpl σ
  | seq     : CSimpl σ → CSimpl σ → CSimpl σ
  | cond    : (σ → Bool) → CSimpl σ → CSimpl σ → CSimpl σ
  | while   : (σ → Bool) → CSimpl σ → CSimpl σ
  | call    : ProcName → CSimpl σ
  | guard   : (σ → Prop) → CSimpl σ → CSimpl σ
  | throw   : CSimpl σ
  | catch   : CSimpl σ → CSimpl σ → CSimpl σ
  | spec    : (σ → σ → Prop) → CSimpl σ
  | dynCom  : (σ → CSimpl σ) → CSimpl σ

