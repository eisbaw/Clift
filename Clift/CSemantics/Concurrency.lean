-- Concurrency: Interrupt preemption model and shared state verification
--
-- Task 0164: Define the execution model extension for interrupt preemption.
-- This is DEFINITIONS + EXAMPLE, not full concurrency verification.
--
-- Key ideas:
-- 1. PreemptionPoint: a point in sequential code where an ISR may fire
-- 2. Volatile reads: nondeterministic (ISR may have written)
-- 3. Interrupt disable/enable: state operations on an irq_enabled flag
-- 4. ISR and main share heap — PreemptionPoint lets ISR body interleave
--
-- Trust model: ISR bodies are user-supplied CSimpl terms. The framework
-- axiomatizes nothing — it just provides the interleaving model.
--
-- Reference: seL4 proves correctness under interrupts by showing the kernel
-- runs with interrupts disabled at critical points. We replicate this pattern.

import Clift.CSemantics.CSimpl
import Clift.CSemantics.Exec
import Clift.CSemantics.State

/-! # Interrupt state extension -/

/-- Extension to program state for interrupt-aware execution.
    Parametric: wraps any base state σ with interrupt control. -/
structure IrqState (σ : Type) where
  /-- Base program state (heap, locals, etc.) -/
  base : σ
  /-- Whether interrupts are currently enabled -/
  irqEnabled : Bool
  deriving Repr

/-! # Interrupt primitives as CSimpl terms -/

namespace Concurrency

variable {σ : Type}

/-- Disable interrupts: sets irqEnabled to false.
    Models `__disable_irq()` or `cli` instruction. -/
def disableIrq : CSimpl (IrqState σ) :=
  .basic (fun s => { s with irqEnabled := false })

/-- Enable interrupts: sets irqEnabled to true.
    Models `__enable_irq()` or `sti` instruction. -/
def enableIrq : CSimpl (IrqState σ) :=
  .basic (fun s => { s with irqEnabled := true })

/-- Volatile read: modeled as nondeterministic.
    The ISR may have written any value, so the read returns an
    arbitrary value satisfying the relation.

    `volatileRead rel` produces a new state s' such that `rel s s'`.
    Typically rel constrains only the local that receives the value. -/
def volatileRead (rel : IrqState σ → IrqState σ → Prop) : CSimpl (IrqState σ) :=
  .spec rel

/-- Preemption point: if interrupts are enabled, the ISR body may execute.
    If interrupts are disabled, this is a no-op.

    This is the key interleaving primitive. Insert `preemptionPoint isr`
    between any two statements to model possible ISR execution.

    The ISR body is a CSimpl term over the SAME state type (shared heap). -/
def preemptionPoint (isrBody : CSimpl (IrqState σ)) : CSimpl (IrqState σ) :=
  .dynCom (fun s =>
    if s.irqEnabled then
      -- ISR fires: run ISR body, then restore irqEnabled to its pre-ISR value.
      -- Real hardware saves/restores interrupt state on ISR entry/exit.
      .seq isrBody (.basic (fun s' => { s' with irqEnabled := s.irqEnabled }))
    else
      -- Interrupts disabled: no preemption, skip.
      .skip)

/-- Critical section: disable interrupts, run body, re-enable.
    This is the standard pattern for protecting shared state. -/
def criticalSection (body : CSimpl (IrqState σ)) : CSimpl (IrqState σ) :=
  .seq disableIrq (.seq body enableIrq)

/-! # Shared state model -/

/-- A shared variable is accessed by both main code and ISR.
    We model this as a projection from the base state.
    No special type needed — it's just a lens into σ. -/
structure SharedVar (σ : Type) (α : Type) where
  /-- Read the shared variable from state -/
  get : σ → α
  /-- Write the shared variable into state -/
  set : σ → α → σ

/-! # Critical section correctness -/

/-- A critical section is correct if: within the body, no preemption
    point can fire (because irqEnabled = false throughout).

    This is stated as: if we start with irqEnabled = false, and the body
    does not re-enable interrupts, then no preemptionPoint in the body
    will execute the ISR. -/
def criticalSectionInvariant (s : IrqState σ) : Prop :=
  s.irqEnabled = false

/-- After disableIrq, the critical section invariant holds. -/
theorem disableIrq_establishes_critical {s : IrqState σ} {Γ : ProcEnv (IrqState σ)}
    {t : Outcome (IrqState σ)} (h : Exec Γ (disableIrq (σ := σ)) s t) :
    ∀ s', t = .normal s' → criticalSectionInvariant s' := by
  intro s' ht
  cases h with
  | basic _ _ =>
    simp at ht
    cases ht
    rfl

/-- After enableIrq, interrupts are enabled. -/
theorem enableIrq_restores {s : IrqState σ} {Γ : ProcEnv (IrqState σ)}
    {t : Outcome (IrqState σ)} (h : Exec Γ (enableIrq (σ := σ)) s t) :
    ∀ s', t = .normal s' → s'.irqEnabled = true := by
  intro s' ht
  cases h with
  | basic _ _ =>
    simp at ht
    cases ht
    rfl

/-! # Example: ISR writing to shared ring buffer with disable_irq guard

Scenario:
- Main code writes to a ring buffer (producer)
- ISR reads from the ring buffer (consumer)
- Shared state: head index, tail index, count, buffer array
- Critical section around main's write prevents ISR from seeing inconsistent state

We model this at the CSimpl level, NOT at the proof level.
The full proof would require FuncSpecs for the ISR and main, which is task-level work.
Here we just show the STRUCTURE. -/

/-- Example ring buffer shared state -/
structure SharedRingBuf where
  head : UInt32
  tail : UInt32
  count : UInt32
  capacity : UInt32
  deriving Repr

/-- Example: ISR body that reads from ring buffer (consumer).
    This reads head, decrements count, advances head. -/
def exampleIsrBody : CSimpl (IrqState SharedRingBuf) :=
  .cond (fun s => decide (s.base.count > 0))
    -- Non-empty: consume one element
    (.basic (fun s => { s with base := {
      s.base with
        head := s.base.head + 1   -- simplified, should be mod capacity
        count := s.base.count - 1
    }}))
    -- Empty: nothing to consume
    .skip

/-- Example: main code that writes to ring buffer with critical section.
    The critical section prevents the ISR from firing between the
    tail update and the count update. -/
def exampleMainWrite : CSimpl (IrqState SharedRingBuf) :=
  criticalSection (
    .cond (fun s => decide (s.base.count < s.base.capacity))
      -- Not full: produce one element
      (.basic (fun s => { s with base := {
        s.base with
          tail := s.base.tail + 1   -- simplified
          count := s.base.count + 1
      }}))
      -- Full: skip (or return error)
      .skip
  )

/-- The invariant for the shared ring buffer: count <= capacity.
    Must hold at every preemption point. -/
def rbSharedInvariant (s : IrqState SharedRingBuf) : Prop :=
  s.base.count.toNat ≤ s.base.capacity.toNat

/-! # Documentation

## How to use the concurrency model

1. Wrap your state type with `IrqState σ` to add interrupt control.

2. Define ISR bodies as `CSimpl (IrqState σ)` terms.

3. Insert `preemptionPoint isrBody` between statements where the ISR
   may fire. In practice, preemption can happen between any two
   non-atomic C statements.

4. Protect shared state with `criticalSection body` which wraps the
   body in disable_irq / enable_irq.

5. Prove that:
   a. The shared invariant is preserved by the ISR body
   b. The shared invariant is preserved by main code (including
      the critical section)
   c. At every preemption point, the invariant holds

## Limitations

- This is an INTERLEAVING model, not a true concurrency model.
  It handles single-ISR preemption of sequential code.
- Multi-level interrupt priority (nested ISRs) is not modeled.
- Memory barriers / cache coherence are not modeled.
- The model assumes ISRs run to completion (no preemption of ISRs).

## What enters the TCB

Nothing — the model is purely definitional. The user must correctly
place preemption points and correctly model their ISR body. If the
model is wrong (e.g., missing a preemption point), proofs are valid
but don't apply to the real system.
-/

end Concurrency
