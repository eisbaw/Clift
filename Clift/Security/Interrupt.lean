-- Interrupt Handling Verification Pattern
--
-- Defines the verification pattern for interrupt management as in seL4.
-- Key concerns: interrupts are correctly acknowledged to hardware, correctly
-- delegated to user-space handlers, and interrupt state (masked/pending)
-- remains consistent.
--
-- This is a VERIFICATION PATTERN, not a full implementation.
--
-- Reference: seL4 TOCS 2014 (interrupt handling verification)

namespace InterruptVerification

/-! # Interrupt Types -/

/-- Interrupt request number (hardware IRQ line). -/
structure IrqNum where
  val : Nat
  deriving DecidableEq, BEq, Repr

/-- Interrupt handler endpoint: where the kernel delivers interrupt notifications. -/
structure HandlerEndpoint where
  id : Nat
  deriving DecidableEq, BEq, Repr

/-- State of a single interrupt line. -/
inductive IrqLineState where
  | inactive    -- no handler registered
  | active      -- handler registered, interrupt enabled
  | masked      -- handler registered, interrupt temporarily disabled
  deriving DecidableEq, BEq, Repr

/-! # Interrupt State -/

/-- Handler table entry: maps an IRQ to its handler endpoint and state. -/
structure IrqEntry where
  lineState : IrqLineState
  handler   : Option HandlerEndpoint
  pending   : Bool           -- interrupt fired but not yet acknowledged
  deriving DecidableEq, BEq, Repr

/-- System interrupt state. -/
structure IrqState where
  table    : IrqNum → IrqEntry
  maxIrq   : Nat
  inHandler : Bool           -- true while kernel is processing an interrupt

/-! # Interrupt Operations -/

/-- Register a handler for an IRQ. Precondition: IRQ is currently inactive. -/
def registerHandler (s : IrqState) (irq : IrqNum) (ep : HandlerEndpoint)
    : Option IrqState :=
  let entry := s.table irq
  if entry.lineState ≠ .inactive then none
  else
    let newTable := fun i =>
      if i = irq then { lineState := .active, handler := some ep, pending := false }
      else s.table i
    some { s with table := newTable }

/-- Handle an incoming interrupt: mark as pending, mask the line. -/
def handleIrq (s : IrqState) (irq : IrqNum) : IrqState :=
  let entry := s.table irq
  { s with
    table := fun i =>
      if i = irq then { entry with pending := true, lineState := .masked }
      else s.table i
    inHandler := true }

/-- Acknowledge an interrupt: clear pending, unmask the line. -/
def ackIrq (s : IrqState) (irq : IrqNum) : IrqState :=
  let entry := s.table irq
  { s with
    table := fun i =>
      if i = irq then { entry with pending := false, lineState := .active }
      else s.table i
    inHandler := false }

/-- Mask an interrupt line (temporarily disable). -/
def maskIrq (s : IrqState) (irq : IrqNum) : IrqState :=
  let entry := s.table irq
  { s with table := fun i =>
    if i = irq then { entry with lineState := .masked }
    else s.table i }

/-! # Key Properties -/

/-- Handler invoked: when an IRQ fires, the registered handler is notified.
    Stated as: if an IRQ is pending and has an active handler, the handler
    endpoint will receive a notification. -/
def handlerInvoked (s : IrqState) : Prop :=
  ∀ (irq : IrqNum) (entry : IrqEntry),
    s.table irq = entry →
    entry.pending = true →
    -- There must be a handler registered
    entry.handler ≠ none

/-- Mask consistency: a masked IRQ cannot fire (become pending).
    This models the hardware contract: masking prevents new interrupts. -/
def maskConsistency (pre post : IrqState) : Prop :=
  ∀ (irq : IrqNum),
    (pre.table irq).lineState = .masked →
    (pre.table irq).pending = false →
    -- A masked, non-pending IRQ stays non-pending
    (post.table irq).pending = false

/-- Acknowledgment correctness: after ackIrq, the IRQ is no longer pending
    and the line is re-enabled. -/
theorem ack_clears_pending (s : IrqState) (irq : IrqNum) :
    (ackIrq s irq).table irq = { (s.table irq) with pending := false, lineState := .active } := by
  simp [ackIrq]

/-- Handler isolation: handling one IRQ does not affect other IRQ entries. -/
theorem handleIrq_isolation (s : IrqState) (irq other : IrqNum) (h : irq ≠ other) :
    (handleIrq s irq).table other = s.table other := by
  simp [handleIrq, Ne.symm h]

/-- No spurious state changes: inactive IRQs remain inactive across operations. -/
def inactiveStable (pre post : IrqState) : Prop :=
  ∀ (irq : IrqNum),
    (pre.table irq).lineState = .inactive →
    (post.table irq).lineState = .inactive

/-! # Verification Pattern

To verify C interrupt handling with Clift:

1. Import interrupt controller driver C code
   - Exercises: memory-mapped I/O (modeled as volatile reads/writes),
     bitwise operations on interrupt registers
2. Define AbstractSpec with: registerHandler, handleIrq, ackIrq, mask/unmask
3. Prove refinement: C register manipulation correctly implements the abstract model
4. Prove handlerInvoked: pending IRQs always have handlers
5. Prove maskConsistency: masked IRQs don't generate spurious interrupts
6. Prove handleIrq_isolation: IRQ handling doesn't corrupt other entries

Key challenge: interrupt handlers run asynchronously. The concurrency model
(task-0164) must ensure that kernel state is consistent when interrupted.
-/

end InterruptVerification
