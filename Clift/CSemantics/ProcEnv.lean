-- Procedure environment: maps procedure names to CSimpl bodies
--
-- Following Simpl: the procedure environment Γ maps procedure names
-- to their CSimpl bodies. Used by the Exec relation for call resolution.
--
-- Reference: Simpl Language.thy (procedures locale)

import Clift.CSemantics.CSimpl

/-! # Procedure environment -/

/-- Maps procedure names to their CSimpl command bodies.
    Partial function: returns none if the procedure is not defined.

    This is the Lean equivalent of Simpl's Γ parameter. -/
def ProcEnv (σ : Type) := ProcName → Option (CSimpl σ)

namespace ProcEnv

variable {σ : Type}

/-- Empty procedure environment (no procedures defined). -/
def empty : ProcEnv σ := fun _ => none

/-- Extend a procedure environment with a new binding. -/
def insert (Γ : ProcEnv σ) (name : ProcName) (body : CSimpl σ) : ProcEnv σ :=
  fun n => if n == name then some body else Γ n

/-- Lookup a procedure by name. -/
def lookup (Γ : ProcEnv σ) (name : ProcName) : Option (CSimpl σ) :=
  Γ name

end ProcEnv
