-- Task 0147: UART driver verification
--
-- Real-world target: UART driver with MMIO register manipulation.
-- 15 functions imported from uart_driver.c (~280 LOC C -> ~1280 lines Lean).
--
-- Key verification targets:
-- - Driver state machine transitions (uninit -> configured -> active -> error)
-- - Register values set correctly by init/enable/disable
-- - Error handling: every error path returns correct error code
-- - Receive buffer invariant maintained

import Generated.UartDriver
import Clift.Lifting.Pipeline
import Clift.Lifting.FuncSpec

set_option maxHeartbeats 12800000
set_option maxRecDepth 4096

open UartDriver

/-! # Step 1: Run the clift pipeline on all 15 functions -/

clift UartDriver

/-! # Step 2: Verify L1 definitions exist for all functions -/

-- Init + config (4)
#check @UartDriver.l1_uart_init_body
#check @UartDriver.l1_uart_set_baud_body
#check @UartDriver.l1_uart_enable_body
#check @UartDriver.l1_uart_disable_body

-- TX/RX (3)
#check @UartDriver.l1_uart_send_byte_body
#check @UartDriver.l1_uart_poll_rx_body
#check @UartDriver.l1_uart_read_byte_body

-- Status queries (6)
#check @UartDriver.l1_uart_get_state_body
#check @UartDriver.l1_uart_get_tx_count_body
#check @UartDriver.l1_uart_get_rx_count_body
#check @UartDriver.l1_uart_get_error_count_body
#check @UartDriver.l1_uart_rx_buf_level_body
#check @UartDriver.l1_uart_rx_buf_empty_body

-- Error handling (2)
#check @UartDriver.l1_uart_check_errors_body
#check @UartDriver.l1_uart_reset_error_body

/-! # Step 3: FuncSpecs for key driver functions -/

/-- Driver state constants as Lean values -/
def DRV_UNINIT     : UInt32 := 0
def DRV_CONFIGURED : UInt32 := 1
def DRV_ACTIVE     : UInt32 := 2
def DRV_ERROR      : UInt32 := 3

/-- uart_init: initializes all driver fields.
    Precondition: valid pointers, clock_freq > 0, rx_capacity > 0.
    Postcondition: all fields zeroed/set, state = UNINIT. -/
def uart_init_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.drv ∧
    heapPtrValid s.globals.rawHeap s.locals.regs ∧
    s.locals.clock_freq ≠ 0 ∧
    s.locals.rx_capacity ≠ 0
  post := fun r s =>
    r = Except.ok () →
    s.locals.ret__val = 0 ∧
    let drv := hVal s.globals.rawHeap s.locals.drv
    drv.state = DRV_UNINIT ∧
    drv.baud_rate = 0 ∧
    drv.tx_count = 0 ∧
    drv.rx_count = 0 ∧
    drv.error_count = 0 ∧
    drv.rx_buf_count = 0

/-- uart_get_state: pure accessor, returns state field. -/
def uart_get_state_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.drv
  post := fun r s =>
    r = Except.ok () →
    s.locals.ret__val = (hVal s.globals.rawHeap s.locals.drv).state

/-- uart_enable: transitions from CONFIGURED to ACTIVE.
    Sets control register to enable TX+RX, enables interrupts. -/
def uart_enable_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.drv ∧
    (hVal s.globals.rawHeap s.locals.drv).state = DRV_CONFIGURED ∧
    heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.drv).regs
  post := fun r s =>
    r = Except.ok () →
    s.locals.ret__val = 0 ∧
    (hVal s.globals.rawHeap s.locals.drv).state = DRV_ACTIVE

/-- uart_rx_buf_empty: returns 1 if rx_buf_count == 0. -/
def uart_rx_buf_empty_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.drv
  post := fun r s =>
    r = Except.ok () →
    ((hVal s.globals.rawHeap s.locals.drv).rx_buf_count = 0 →
      s.locals.ret__val = 1) ∧
    ((hVal s.globals.rawHeap s.locals.drv).rx_buf_count ≠ 0 →
      s.locals.ret__val = 0)

/-- uart_reset_error: transitions from ERROR back to CONFIGURED.
    Returns UART_ERR_STATE (1) if not in ERROR state. -/
def uart_reset_error_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.drv ∧
    heapPtrValid s.globals.rawHeap (hVal s.globals.rawHeap s.locals.drv).regs
  post := fun r s =>
    r = Except.ok () →
    -- Either error was reset successfully, or wrong state error returned
    (s.locals.ret__val = 0 ∨ s.locals.ret__val = 1)

/-! # Step 4: validHoare theorems -/

theorem uart_init_satisfies_spec :
    uart_init_spec.satisfiedBy (l1_uart_init_body) := by
  unfold FuncSpec.satisfiedBy uart_init_spec
  unfold validHoare
  intro s hpre
  sorry -- Requires: heap write reasoning for 11 field assignments

private theorem uart_retval_globals (s : ProgramState) (v : UInt32) :
    ({ s with locals := { s.locals with ret__val := v } } : ProgramState).globals = s.globals := rfl
private theorem uart_retval_drv (s : ProgramState) (v : UInt32) :
    ({ s with locals := { s.locals with ret__val := v } } : ProgramState).locals.drv = s.locals.drv := rfl
private theorem uart_retval_val (s : ProgramState) (v : UInt32) :
    ({ s with locals := { s.locals with ret__val := v } } : ProgramState).locals.ret__val = v := rfl

attribute [local irreducible] hVal heapPtrValid in
theorem uart_get_state_satisfies_spec :
    uart_get_state_spec.satisfiedBy (l1_uart_get_state_body) := by
  unfold FuncSpec.satisfiedBy uart_get_state_spec validHoare
  intro s hpre
  unfold UartDriver.l1_uart_get_state_body
  have h := L1_guard_modify_throw_catch_skip_result
    (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.drv)
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := (hVal s.globals.rawHeap s.locals.drv).state } })
    s hpre
  obtain ⟨h_res, h_nf⟩ := h
  constructor
  · exact h_nf
  · intro r s' h_mem _
    rw [h_res] at h_mem
    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
    subst hr; subst hs
    rw [uart_retval_val, uart_retval_globals, uart_retval_drv]

/-! # Step 5: Driver state machine property

  The driver implements a state machine:
    UNINIT --[set_baud]--> CONFIGURED --[enable]--> ACTIVE
    ACTIVE --[disable]--> CONFIGURED
    ACTIVE --[check_errors, if error]--> ERROR
    ERROR  --[reset_error]--> CONFIGURED

  State machine invariant: only valid transitions are allowed.
  Each function checks the current state and returns UART_ERR_STATE (1)
  if called from an invalid state.

  Full state machine verification requires:
  1. Each function preserves the state machine invariant
  2. No function transitions to an undocumented state
  3. Error paths leave state unchanged (except check_errors -> ERROR)

  This is feasible with the current FuncSpec framework but requires
  heap frame reasoning to prove state is preserved.
-/

/-! # Summary

  15 functions imported and lifted through L1/L2/L3.
  5 FuncSpecs defined covering:
    - Initialization (uart_init)
    - State machine transitions (uart_enable, uart_reset_error)
    - Pure accessors (uart_get_state, uart_rx_buf_empty)

  Blocked on:
    - Heap write/read reasoning for register manipulation
    - Double-dereference pattern (drv->regs->field): requires two heap reads
    - State machine invariant proof (needs all transitions verified)

  The MMIO pattern (pointer-to-register-struct) is handled correctly by CImporter.
-/
