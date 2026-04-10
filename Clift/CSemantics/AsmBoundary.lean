-- AsmBoundary: Inline assembly boundary — axiomatized ASM with C/ASM interface
--
-- Task 0167: Define AsmSpec type (FuncSpec without proof — axiomatized).
-- CImporter recognizes `__asm__` or stub functions and emits axiomatized procs.
--
-- Trust model (same as seL4):
-- - ASM specs are TRUSTED. They enter the TCB.
-- - C code is VERIFIED. It does not enter the TCB.
-- - The boundary is explicit: AsmSpec is clearly marked as axiomatized.
-- - If an AsmSpec is wrong, proofs about C code that calls it are unsound
--   (they prove properties relative to the wrong ASM spec).
--
-- seL4 has ~340 lines of handwritten ARM assembly axiomatized as specs.
-- Real embedded C uses inline asm for: interrupt enable/disable, memory
-- barriers, cache flush, register access.

import Clift.CSemantics.CSimpl
import Clift.CSemantics.Exec

/-! # AsmSpec: axiomatized assembly specification -/

/-- An axiomatized assembly specification.

    Like FuncSpec but WITHOUT a proof obligation. The pre/post are
    ASSUMED correct — they describe what the assembly does, and we
    trust that description.

    Every AsmSpec enters the Trusted Computing Base (TCB).

    Fields:
    - `name`: human-readable name for documentation
    - `pre`: precondition the assembly requires (caller must establish)
    - `post`: postcondition the assembly guarantees (relation on states)
    - `tcbJustification`: why we trust this spec (documentation) -/
structure AsmSpec (σ : Type) where
  /-- Name of the assembly routine -/
  name : String
  /-- Precondition: what must hold before the ASM executes -/
  pre : σ → Prop
  /-- Postcondition: relation between pre-state and post-state -/
  post : σ → σ → Prop
  /-- TCB justification: why we trust this spec is correct.
      This is documentation only — not checked by Lean. -/
  tcbJustification : String

/-! # Converting AsmSpec to CSimpl -/

namespace AsmSpec

variable {σ : Type}

/-- Convert an AsmSpec to a CSimpl term.
    The result is a guarded nondeterministic spec:
    - Guard: precondition must hold (fault if violated)
    - Spec: postcondition constrains the result (nondeterministic choice)

    This is how the CImporter emits `__asm__` blocks:
    `guard pre (spec post)` -/
def toCSimpl (spec : AsmSpec σ) : CSimpl σ :=
  .guard spec.pre (.spec spec.post)

/-- Convert an AsmSpec to a CSimpl procedure entry in a ProcEnv.
    The name is the procedure name used by CSimpl.call. -/
def toProcEntry (spec : AsmSpec σ) : ProcName × CSimpl σ :=
  (spec.name, spec.toCSimpl)

end AsmSpec

/-! # Registry of axiomatized procedures -/

/-- A collection of axiomatized ASM specs for a program.
    This is the complete TCB for assembly in a verified program. -/
structure AsmRegistry (σ : Type) where
  /-- All axiomatized ASM specs -/
  specs : List (AsmSpec σ)

namespace AsmRegistry

variable {σ : Type}

/-- Get all procedure names that are axiomatized (in the TCB). -/
def tcbNames (reg : AsmRegistry σ) : List String :=
  reg.specs.map (·.name)

/-- Convert the registry to ProcEnv entries. -/
def toProcEntries (reg : AsmRegistry σ) : List (ProcName × CSimpl σ) :=
  reg.specs.map (·.toProcEntry)

end AsmRegistry

/-! # Standard ASM specs for embedded systems -/

/-- Axiomatized spec for `disable_irq()` / `cpsid i` / `cli`.
    Postcondition: interrupts are disabled in the state.
    Requires: state has an `irqEnabled` field (or equivalent).

    This is parameterized by a lens into the irq-enabled flag. -/
def asmDisableIrq {σ : Type} (getIrq : σ → Bool) (_setIrq : σ → Bool → σ) : AsmSpec σ where
  name := "disable_irq"
  pre := fun _ => True  -- always safe to disable interrupts
  post := fun _s s' => getIrq s' = false
  tcbJustification := "ARM: cpsid i clears the I bit in CPSR, disabling IRQs. \
    x86: cli clears IF in EFLAGS. Both are single instructions with \
    well-defined semantics."

/-- Axiomatized spec for `enable_irq()` / `cpsie i` / `sti`. -/
def asmEnableIrq {σ : Type} (getIrq : σ → Bool) (_setIrq : σ → Bool → σ) : AsmSpec σ where
  name := "enable_irq"
  pre := fun _ => True
  post := fun _s s' => getIrq s' = true
  tcbJustification := "ARM: cpsie i sets the I bit in CPSR, enabling IRQs. \
    x86: sti sets IF in EFLAGS."

/-- Axiomatized spec for a memory barrier (`dmb`, `dsb`, `mfence`).
    Effect: no state change visible at the C level, but prevents
    reordering of memory operations. Modeled as skip since our
    sequential memory model has no reordering. -/
def asmMemoryBarrier {σ : Type} : AsmSpec σ where
  name := "memory_barrier"
  pre := fun _ => True
  post := fun s s' => s' = s  -- no visible state change
  tcbJustification := "Memory barriers prevent hardware reordering. \
    In our sequential model, all memory operations are already ordered. \
    The barrier is a no-op but must be present for real hardware correctness."

/-- Axiomatized spec for cache flush.
    Effect: no state change at the C abstraction level.
    The C memory model does not distinguish cached vs uncached. -/
def asmCacheFlush {σ : Type} : AsmSpec σ where
  name := "cache_flush"
  pre := fun _ => True
  post := fun s s' => s' = s
  tcbJustification := "Cache flush ensures coherence between cache and main memory. \
    Our memory model is cache-transparent (single copy), so this is a no-op. \
    Required for DMA correctness on real hardware."

/-! # Example: disable_irq/enable_irq as axiomatized procs -/

namespace AsmExample

/-- Example state with an interrupt flag -/
structure ExState where
  irqEnabled : Bool
  data : Nat
  deriving Repr

def exDisableIrq : AsmSpec ExState :=
  asmDisableIrq (·.irqEnabled) (fun s b => { s with irqEnabled := b })

def exEnableIrq : AsmSpec ExState :=
  asmEnableIrq (·.irqEnabled) (fun s b => { s with irqEnabled := b })

/-- Example registry for a program using IRQ control -/
def exRegistry : AsmRegistry ExState :=
  { specs := [exDisableIrq, exEnableIrq] }

/-- Example: calling disable_irq via CSimpl.call.
    The CImporter would emit this for `__asm__ volatile("cpsid i")`. -/
def exCriticalSection : CSimpl ExState :=
  .seq (.call "disable_irq")
    (.seq (.basic (fun s => { s with data := s.data + 1 }))
      (.call "enable_irq"))

/-- The procedure environment includes the axiomatized procs. -/
def exProcEnv : ProcEnv ExState := fun name =>
  match name with
  | "disable_irq" => some exDisableIrq.toCSimpl
  | "enable_irq" => some exEnableIrq.toCSimpl
  | _ => none

/-- After disable_irq executes normally, interrupts are disabled. -/
theorem exDisableIrq_post (s : ExState) (s' : ExState)
    (h : Exec exProcEnv (.call "disable_irq") s (.normal s')) :
    s'.irqEnabled = false := by
  -- Unfold the call: exProcEnv "disable_irq" = some (guard True (spec post))
  cases h with
  | callDefined _ body _ _ h_lookup h_exec =>
    simp [exProcEnv] at h_lookup
    subst h_lookup
    -- Body is: guard pre (spec post) = guard (fun _ => True) (spec ...)
    -- Body is: guard pre (spec post)
    cases h_exec
    case guardOk h_pre h_spec_exec =>
      cases h_spec_exec
      case specNormal h_rel => exact h_rel

end AsmExample

/-! # CImporter integration

## Recognition rules

The CImporter recognizes `__asm__` blocks via two patterns:

1. **Inline asm**: `__asm__ volatile("cpsid i")` — replaced with
   `CSimpl.call "disable_irq"` and an AsmSpec entry.

2. **Stub functions**: Functions declared `extern` with no body that
   are known assembly routines (e.g., `extern void disable_irq(void);`
   with a companion AsmSpec).

## Generated code

For each recognized assembly routine, the CImporter emits:

```lean
-- TCB: axiomatized ASM spec
def asm_disable_irq : AsmSpec ProgramState := {
  name := "disable_irq"
  pre := fun _ => True
  post := fun _ s' => s'.globals.irqEnabled = false
  tcbJustification := "cpsid i on ARM"
}

-- In procEnv:
| "disable_irq" => some asm_disable_irq.toCSimpl
```

## TCB documentation

Every AsmSpec must be listed in docs/tcb.md with:
1. The assembly instruction(s) it models
2. The architecture(s) it applies to
3. Why the pre/post spec is believed correct
4. A reference to the architecture manual (ARM ARM, Intel SDM, etc.)
-/
