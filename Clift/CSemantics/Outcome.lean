-- Execution outcomes: normal, abrupt (break/return), fault (UB)
--
-- Following Simpl's xstate/Outcome type.
-- These are the possible results of executing a CSimpl command.
--
-- Reference: plan.md Decision 5
-- Reference: Simpl Semantic.thy (xstate datatype)

/-! # Execution outcomes -/

/-- The outcome of executing a CSimpl command.
    - `normal s`: command completed normally, final state is s
    - `abrupt s`: command exited abruptly (break/continue/return/throw), state is s
    - `fault`:    undefined behavior triggered (guard violation)

    Note: `fault` carries no state — once UB occurs, the state is meaningless.
    This matches Simpl's treatment of Fault states.

    Design: Simpl has a fourth outcome `Stuck` (semantically undefined,
    e.g. missing procedure body). We merge Stuck into `fault` because:
    (a) both represent undefined behavior in C, (b) our ProcEnv is total
    (no missing bodies), (c) fewer cases in every proof.
    See ADR-005 (backlog/docs/adr-005-stuck-merged-into-fault.md).

    The abrupt outcome is used for C's non-local control flow:
    - `throw` produces abrupt
    - `catch` handles abrupt by running the handler
    - `break`/`continue`/`return` are desugared into throw+catch by the importer -/
inductive Outcome (σ : Type) where
  | normal : σ → Outcome σ
  | abrupt : σ → Outcome σ
  | fault  : Outcome σ
  deriving Repr

namespace Outcome

variable {σ : Type}

/-- Extract the state from a normal or abrupt outcome, if present. -/
def state? : Outcome σ → Option σ
  | normal s => some s
  | abrupt s => some s
  | fault    => none

/-- Test if the outcome is normal. -/
def isNormal : Outcome σ → Bool
  | normal _ => true
  | _        => false

/-- Test if the outcome is abrupt. -/
def isAbrupt : Outcome σ → Bool
  | abrupt _ => true
  | _        => false

/-- Test if the outcome is a fault. -/
def isFault : Outcome σ → Bool
  | fault => true
  | _     => false

/-- Map a function over the state in an outcome. -/
def map (f : σ → σ) : Outcome σ → Outcome σ
  | normal s => normal (f s)
  | abrupt s => abrupt (f s)
  | fault    => fault

end Outcome
