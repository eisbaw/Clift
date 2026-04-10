-- Exception / Fault Delivery Verification Pattern
--
-- Defines the verification pattern for CPU exception handling as in seL4.
-- When a user thread causes a fault (page fault, undefined instruction, etc.),
-- the kernel must deliver it to the correct user-space fault handler with
-- the correct fault information.
--
-- This is a VERIFICATION PATTERN, not a full implementation.
-- This is distinct from CSimpl's .fault outcome (which models UB in C);
-- this models the kernel's exception handling mechanism.
--
-- Reference: seL4 TOCS 2014 (exception handling)

/-! # Fault Types -/

/-- CPU exception types that the kernel must handle. -/
inductive FaultType where
  | pageFault           -- invalid memory access
  | undefinedInsn       -- undefined instruction
  | syscallFault        -- invalid syscall arguments
  | capFault            -- capability lookup failure
  | vmFault             -- virtual memory fault (TLB miss after walk)
  | debugFault          -- hardware debug exception (breakpoint)
  deriving DecidableEq, Repr

/-- Fault information captured by the hardware/kernel at fault time. -/
structure FaultInfo where
  faultType : FaultType
  faultAddr : Nat          -- address that caused the fault (for page/VM faults)
  errorCode : Nat          -- hardware error code
  faultPC   : Nat          -- instruction pointer at fault
  deriving DecidableEq, Repr

/-- Fault handler endpoint: where fault notifications are delivered. -/
structure FaultEndpoint where
  id : Nat
  deriving DecidableEq, BEq, Repr

/-- Thread ID for the faulting thread. -/
structure FaultThreadId where
  val : Nat
  deriving DecidableEq, BEq, Repr

/-! # Fault Delivery State -/

/-- Per-thread fault handler configuration. -/
structure ThreadFaultConfig where
  handler  : Option FaultEndpoint    -- where to send faults
  tcbPtr   : Nat                     -- thread control block address

/-- Fault delivery state: tracks pending faults and handler configuration. -/
structure FaultState where
  configs     : FaultThreadId → ThreadFaultConfig
  pendingFault : Option (FaultThreadId × FaultInfo)
  delivered   : List (FaultEndpoint × FaultInfo)   -- audit trail

/-! # Fault Delivery Operation -/

/-- Deliver a fault to the appropriate handler.
    Looks up the faulting thread's handler endpoint and sends the fault info. -/
def deliverFault (s : FaultState) (tid : FaultThreadId) (fault : FaultInfo)
    : Option FaultState :=
  let config := s.configs tid
  match config.handler with
  | none => none    -- no handler configured; thread is killed (modeled as failure)
  | some ep =>
    some { s with
      pendingFault := none
      delivered := (ep, fault) :: s.delivered }

/-! # Key Properties -/

/-- Fault reaches handler: if a thread has a fault handler configured,
    delivering a fault to that thread will result in the handler receiving
    the fault info. This is the main correctness property. -/
def faultReachesHandler (s : FaultState) : Prop :=
  ∀ (tid : FaultThreadId) (fault : FaultInfo) (ep : FaultEndpoint),
    (s.configs tid).handler = some ep →
    ∃ s', deliverFault s tid fault = some s' ∧
          (ep, fault) ∈ s'.delivered

/-- Prove faultReachesHandler holds for our deliverFault implementation. -/
theorem faultReachesHandler_holds (s : FaultState) : faultReachesHandler s := by
  intro tid fault ep h_handler
  refine ⟨?_, ?_, ?_⟩
  · exact { s with pendingFault := none, delivered := (ep, fault) :: s.delivered }
  · simp [deliverFault, h_handler]
  · simp

/-- Fault info integrity: the fault information delivered to the handler
    exactly matches what the hardware reported. No field is dropped or corrupted. -/
def faultInfoIntegrity (s s' : FaultState) (tid : FaultThreadId) (fault : FaultInfo) : Prop :=
  deliverFault s tid fault = some s' →
  ∀ (ep : FaultEndpoint) (delivered_fault : FaultInfo),
    (ep, delivered_fault) ∈ s'.delivered →
    (ep, delivered_fault) ∉ s.delivered →
    delivered_fault = fault

/-- No phantom faults: a fault delivery does not create fault records for
    endpoints that are not the handler of the faulting thread. -/
def noPhantomFaults (s s' : FaultState) (tid : FaultThreadId) (fault : FaultInfo) : Prop :=
  deliverFault s tid fault = some s' →
  ∀ (ep : FaultEndpoint) (f : FaultInfo),
    (ep, f) ∈ s'.delivered →
    (ep, f) ∉ s.delivered →
    (s.configs tid).handler = some ep

/-! # Verification Pattern

To verify C fault delivery with Clift:

1. Import the kernel's fault handling C code
   - Exercises: switch/case on fault type, struct access for TCB fields,
     IPC message construction for fault delivery
2. Define AbstractSpec with: deliverFault, setFaultHandler, clearFault
3. Prove refinement: C IPC message construction matches abstract fault info
4. Prove faultReachesHandler: configured handlers receive faults
5. Prove faultInfoIntegrity: delivered fault info is accurate
6. Prove noPhantomFaults: no spurious fault deliveries

Key challenge: fault delivery involves IPC (sending a message to the handler
endpoint). The IPC mechanism itself needs separate verification.
-/
