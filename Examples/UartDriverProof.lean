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

/-! ## uart_init: anonymous constructor for ret__val update (16-field Locals) -/

private noncomputable def uart_f_ret (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.baud_rate, s.locals.byte_val, s.locals.clock_freq,
    s.locals.cr, s.locals.data, s.locals.denominator, s.locals.divisor,
    s.locals.drv, s.locals.errors, s.locals.front, s.locals.node,
    s.locals.out_byte, s.locals.regs, 0, s.locals.rx_capacity, s.locals.sr⟩⟩

attribute [local irreducible] hVal heapUpdate in
@[simp] private theorem uart_f_ret_globals (s : ProgramState) :
    (uart_f_ret s).globals = s.globals := by
  show (⟨s.globals, ⟨s.locals.baud_rate, s.locals.byte_val, s.locals.clock_freq,
    s.locals.cr, s.locals.data, s.locals.denominator, s.locals.divisor,
    s.locals.drv, s.locals.errors, s.locals.front, s.locals.node,
    s.locals.out_byte, s.locals.regs, 0, s.locals.rx_capacity, s.locals.sr⟩⟩ :
    ProgramState).globals = _; rfl

private theorem uart_f_ret_locals_eq (s : ProgramState) :
    (uart_f_ret s).locals = ⟨s.locals.baud_rate, s.locals.byte_val, s.locals.clock_freq,
      s.locals.cr, s.locals.data, s.locals.denominator, s.locals.divisor,
      s.locals.drv, s.locals.errors, s.locals.front, s.locals.node,
      s.locals.out_byte, s.locals.regs, 0, s.locals.rx_capacity, s.locals.sr⟩ := by
  show (⟨s.globals, ⟨s.locals.baud_rate, s.locals.byte_val, s.locals.clock_freq,
    s.locals.cr, s.locals.data, s.locals.denominator, s.locals.divisor,
    s.locals.drv, s.locals.errors, s.locals.front, s.locals.node,
    s.locals.out_byte, s.locals.regs, 0, s.locals.rx_capacity, s.locals.sr⟩⟩ :
    ProgramState).locals = _; rfl

@[simp] private theorem uart_f_ret_drv (s : ProgramState) :
    (uart_f_ret s).locals.drv = s.locals.drv := by rw [uart_f_ret_locals_eq]
@[simp] private theorem uart_f_ret_ret_val (s : ProgramState) :
    (uart_f_ret s).locals.ret__val = 0 := by rw [uart_f_ret_locals_eq]

private theorem uart_heapUpdate_drv_ptrValid (s : ProgramState)
    (hv : heapPtrValid s.globals.rawHeap s.locals.drv) (v : C_uart_driver) :
    heapPtrValid (heapUpdate s.globals.rawHeap s.locals.drv v) s.locals.drv :=
  heapUpdate_preserves_heapPtrValid _ _ _ _ hv

theorem uart_init_satisfies_spec :
    uart_init_spec.satisfiedBy (l1_uart_init_body) := by
  unfold FuncSpec.satisfiedBy uart_init_spec validHoare
  dsimp only []
  intro s ⟨hpre_drv, _hpre_regs, hpre_clk, hpre_rxcap⟩
  -- Step functions matching the generated L1 body lambdas exactly.
  -- { s with globals := { s.globals with rawHeap := ... } } is fine for CState/Globals (2+1 fields).
  let p := fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.drv
  let f1 := fun s : ProgramState => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.drv ({ hVal s.globals.rawHeap s.locals.drv with regs := s.locals.regs }) } }
  let f2 := fun s : ProgramState => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.drv ({ hVal s.globals.rawHeap s.locals.drv with state := 0 }) } }
  let f3 := fun s : ProgramState => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.drv ({ hVal s.globals.rawHeap s.locals.drv with baud_rate := 0 }) } }
  let f4 := fun s : ProgramState => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.drv ({ hVal s.globals.rawHeap s.locals.drv with clock_freq := s.locals.clock_freq }) } }
  let f5 := fun s : ProgramState => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.drv ({ hVal s.globals.rawHeap s.locals.drv with tx_count := 0 }) } }
  let f6 := fun s : ProgramState => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.drv ({ hVal s.globals.rawHeap s.locals.drv with rx_count := 0 }) } }
  let f7 := fun s : ProgramState => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.drv ({ hVal s.globals.rawHeap s.locals.drv with error_count := 0 }) } }
  let f8 := fun s : ProgramState => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.drv ({ hVal s.globals.rawHeap s.locals.drv with rx_head := Ptr.null }) } }
  let f9 := fun s : ProgramState => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.drv ({ hVal s.globals.rawHeap s.locals.drv with rx_tail := Ptr.null }) } }
  let f10 := fun s : ProgramState => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.drv ({ hVal s.globals.rawHeap s.locals.drv with rx_buf_count := 0 }) } }
  let f11 := fun s : ProgramState => { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.drv ({ hVal s.globals.rawHeap s.locals.drv with rx_buf_capacity := s.locals.rx_capacity }) } }
  let f_ret := uart_f_ret
  -- Condition true branches (early returns, never taken)
  let cond_true := L1.seq (L1.modify (fun s : ProgramState => { s with locals := { s.locals with ret__val := 2 } })) L1.throw
  -- Intermediate states
  let s1 := f1 s; let s2 := f2 s1; let s3 := f3 s2; let s4 := f4 s3
  let s5 := f5 s4; let s6 := f6 s5; let s7 := f7 s6; let s8 := f8 s7
  let s9 := f9 s8; let s10 := f10 s9; let s11 := f11 s10
  let s_final := f_ret s11
  -- Tail computations (named to avoid unresolvable _ placeholders)
  let tail_ret := L1.seq (L1.modify f_ret) L1.throw
  let tail_11 := L1.seq (L1.seq (L1.guard p) (L1.modify f11)) tail_ret
  let tail_10 := L1.seq (L1.seq (L1.guard p) (L1.modify f10)) tail_11
  let tail_9 := L1.seq (L1.seq (L1.guard p) (L1.modify f9)) tail_10
  let tail_8 := L1.seq (L1.seq (L1.guard p) (L1.modify f8)) tail_9
  let tail_7 := L1.seq (L1.seq (L1.guard p) (L1.modify f7)) tail_8
  let tail_6 := L1.seq (L1.seq (L1.guard p) (L1.modify f6)) tail_7
  let tail_5 := L1.seq (L1.seq (L1.guard p) (L1.modify f5)) tail_6
  let tail_4 := L1.seq (L1.seq (L1.guard p) (L1.modify f4)) tail_5
  let tail_3 := L1.seq (L1.seq (L1.guard p) (L1.modify f3)) tail_4
  let tail_2 := L1.seq (L1.seq (L1.guard p) (L1.modify f2)) tail_3
  let tail_1 := L1.seq (L1.seq (L1.guard p) (L1.modify f1)) tail_2
  let tail_c2 := L1.seq (L1.condition (fun s => decide (s.locals.rx_capacity = 0)) cond_true L1.skip) tail_1
  let tail_c1 := L1.seq (L1.condition (fun s => decide (s.locals.clock_freq = 0)) cond_true L1.skip) tail_c2
  -- heapPtrValid preservation
  have hv1 : p s1 := uart_heapUpdate_drv_ptrValid s hpre_drv _
  have hv2 : p s2 := uart_heapUpdate_drv_ptrValid s1 hv1 _
  have hv3 : p s3 := uart_heapUpdate_drv_ptrValid s2 hv2 _
  have hv4 : p s4 := uart_heapUpdate_drv_ptrValid s3 hv3 _
  have hv5 : p s5 := uart_heapUpdate_drv_ptrValid s4 hv4 _
  have hv6 : p s6 := uart_heapUpdate_drv_ptrValid s5 hv5 _
  have hv7 : p s7 := uart_heapUpdate_drv_ptrValid s6 hv6 _
  have hv8 : p s8 := uart_heapUpdate_drv_ptrValid s7 hv7 _
  have hv9 : p s9 := uart_heapUpdate_drv_ptrValid s8 hv8 _
  have hv10 : p s10 := uart_heapUpdate_drv_ptrValid s9 hv9 _
  have hv11 : p s11 := uart_heapUpdate_drv_ptrValid s10 hv10 _
  -- Guard+modify results
  have h1 := L1_guard_modify_result p f1 s hpre_drv
  have h2 := L1_guard_modify_result p f2 s1 hv1
  have h3 := L1_guard_modify_result p f3 s2 hv2
  have h4 := L1_guard_modify_result p f4 s3 hv3
  have h5 := L1_guard_modify_result p f5 s4 hv4
  have h6 := L1_guard_modify_result p f6 s5 hv5
  have h7 := L1_guard_modify_result p f7 s6 hv6
  have h8 := L1_guard_modify_result p f8 s7 hv7
  have h9 := L1_guard_modify_result p f9 s8 hv8
  have h10 := L1_guard_modify_result p f10 s9 hv9
  have h11 := L1_guard_modify_result p f11 s10 hv10
  -- Modify+throw result
  have h_mt := L1_modify_throw_result f_ret s11
  -- Conditions false
  have hc1 : decide (s.locals.clock_freq = 0) = false := decide_eq_false hpre_clk
  have hc2 : decide (s.locals.rx_capacity = 0) = false := decide_eq_false hpre_rxcap
  -- Condition results (false -> skip -> {(ok, s)})
  have hcond1_res : (L1.condition (fun s => decide (s.locals.clock_freq = 0)) cond_true L1.skip s).results = {(Except.ok (), s)} := by
    show (if decide (s.locals.clock_freq = 0) then cond_true s else L1.skip s).results = _; rw [hc1]; rfl
  have hcond1_nf : ¬(L1.condition (fun s => decide (s.locals.clock_freq = 0)) cond_true L1.skip s).failed := by
    show ¬(if decide (s.locals.clock_freq = 0) then cond_true s else L1.skip s).failed; rw [hc1]; exact id
  have hcond2_res : (L1.condition (fun s => decide (s.locals.rx_capacity = 0)) cond_true L1.skip s).results = {(Except.ok (), s)} := by
    show (if decide (s.locals.rx_capacity = 0) then cond_true s else L1.skip s).results = _; rw [hc2]; rfl
  have hcond2_nf : ¬(L1.condition (fun s => decide (s.locals.rx_capacity = 0)) cond_true L1.skip s).failed := by
    show ¬(if decide (s.locals.rx_capacity = 0) then cond_true s else L1.skip s).failed; rw [hc2]; exact id
  -- Chain from innermost outward
  have hch11 := L1_seq_singleton_ok h11.1 h11.2 (m₂ := tail_ret)
  have hr11 : (tail_11 s10).results = {(Except.error (), s_final)} := by rw [hch11.1, h_mt.1]
  have hn11 : ¬(tail_11 s10).failed := fun hf => h_mt.2 (hch11.2.mp hf)
  have hch10 := L1_seq_singleton_ok h10.1 h10.2 (m₂ := tail_11)
  have hr10 : (tail_10 s9).results = {(Except.error (), s_final)} := by rw [hch10.1, hr11]
  have hn10 : ¬(tail_10 s9).failed := fun hf => hn11 (hch10.2.mp hf)
  have hch9 := L1_seq_singleton_ok h9.1 h9.2 (m₂ := tail_10)
  have hr9 : (tail_9 s8).results = {(Except.error (), s_final)} := by rw [hch9.1, hr10]
  have hn9 : ¬(tail_9 s8).failed := fun hf => hn10 (hch9.2.mp hf)
  have hch8 := L1_seq_singleton_ok h8.1 h8.2 (m₂ := tail_9)
  have hr8 : (tail_8 s7).results = {(Except.error (), s_final)} := by rw [hch8.1, hr9]
  have hn8 : ¬(tail_8 s7).failed := fun hf => hn9 (hch8.2.mp hf)
  have hch7 := L1_seq_singleton_ok h7.1 h7.2 (m₂ := tail_8)
  have hr7 : (tail_7 s6).results = {(Except.error (), s_final)} := by rw [hch7.1, hr8]
  have hn7 : ¬(tail_7 s6).failed := fun hf => hn8 (hch7.2.mp hf)
  have hch6 := L1_seq_singleton_ok h6.1 h6.2 (m₂ := tail_7)
  have hr6 : (tail_6 s5).results = {(Except.error (), s_final)} := by rw [hch6.1, hr7]
  have hn6 : ¬(tail_6 s5).failed := fun hf => hn7 (hch6.2.mp hf)
  have hch5 := L1_seq_singleton_ok h5.1 h5.2 (m₂ := tail_6)
  have hr5 : (tail_5 s4).results = {(Except.error (), s_final)} := by rw [hch5.1, hr6]
  have hn5 : ¬(tail_5 s4).failed := fun hf => hn6 (hch5.2.mp hf)
  have hch4 := L1_seq_singleton_ok h4.1 h4.2 (m₂ := tail_5)
  have hr4 : (tail_4 s3).results = {(Except.error (), s_final)} := by rw [hch4.1, hr5]
  have hn4 : ¬(tail_4 s3).failed := fun hf => hn5 (hch4.2.mp hf)
  have hch3 := L1_seq_singleton_ok h3.1 h3.2 (m₂ := tail_4)
  have hr3 : (tail_3 s2).results = {(Except.error (), s_final)} := by rw [hch3.1, hr4]
  have hn3 : ¬(tail_3 s2).failed := fun hf => hn4 (hch3.2.mp hf)
  have hch2 := L1_seq_singleton_ok h2.1 h2.2 (m₂ := tail_3)
  have hr2 : (tail_2 s1).results = {(Except.error (), s_final)} := by rw [hch2.1, hr3]
  have hn2 : ¬(tail_2 s1).failed := fun hf => hn3 (hch2.2.mp hf)
  have hch1 := L1_seq_singleton_ok h1.1 h1.2 (m₂ := tail_2)
  have hr1 : (tail_1 s).results = {(Except.error (), s_final)} := by rw [hch1.1, hr2]
  have hn1 : ¬(tail_1 s).failed := fun hf => hn2 (hch1.2.mp hf)
  -- Chain condition 2
  have hchc2 := L1_seq_singleton_ok hcond2_res hcond2_nf (m₂ := tail_1)
  have hrc2 : (tail_c2 s).results = {(Except.error (), s_final)} := by rw [hchc2.1, hr1]
  have hnc2 : ¬(tail_c2 s).failed := fun hf => hn1 (hchc2.2.mp hf)
  -- Chain condition 1
  have hchc1 := L1_seq_singleton_ok hcond1_res hcond1_nf (m₂ := tail_c2)
  have hrc1 : (tail_c1 s).results = {(Except.error (), s_final)} := by rw [hchc1.1, hrc2]
  have hnc1 : ¬(tail_c1 s).failed := fun hf => hnc2 (hchc1.2.mp hf)
  -- Catch: error -> skip -> ok result
  have h_catch := L1_catch_error_singleton hrc1 hnc1
  -- The let-bound tail_c1 is definitionally equal to the generated L1 body.
  -- So L1.catch tail_c1 L1.skip matches l1_uart_init_body.
  constructor
  · exact h_catch.2
  · intro r s' h_mem h_ok
    -- h_mem is about l1_uart_init_body which is definitionally L1.catch tail_c1 L1.skip
    have h_mem' : (r, s') ∈ (L1.catch tail_c1 L1.skip s).results := h_mem
    rw [h_catch.1] at h_mem'
    have ⟨hr, hs⟩ := Prod.mk.inj h_mem'
    subst hr; subst hs
    -- Postcondition: chain hVal_heapUpdate_same for each step
    have hb := heapPtrValid_bound hpre_drv
    have hb1 := heapPtrValid_bound hv1
    have hb2 := heapPtrValid_bound hv2
    have hb3 := heapPtrValid_bound hv3
    have hb4 := heapPtrValid_bound hv4
    have hb5 := heapPtrValid_bound hv5
    have hb6 := heapPtrValid_bound hv6
    have hb7 := heapPtrValid_bound hv7
    have hb8 := heapPtrValid_bound hv8
    have hb9 := heapPtrValid_bound hv9
    have hb10 := heapPtrValid_bound hv10
    have h11v : hVal s11.globals.rawHeap s11.locals.drv =
        ({ hVal s10.globals.rawHeap s10.locals.drv with rx_buf_capacity := s10.locals.rx_capacity } : C_uart_driver) :=
      hVal_heapUpdate_same _ _ _ hb10
    have h10v : hVal s10.globals.rawHeap s10.locals.drv =
        ({ hVal s9.globals.rawHeap s9.locals.drv with rx_buf_count := 0 } : C_uart_driver) :=
      hVal_heapUpdate_same _ _ _ hb9
    have h9v : hVal s9.globals.rawHeap s9.locals.drv =
        ({ hVal s8.globals.rawHeap s8.locals.drv with rx_tail := Ptr.null } : C_uart_driver) :=
      hVal_heapUpdate_same _ _ _ hb8
    have h8v : hVal s8.globals.rawHeap s8.locals.drv =
        ({ hVal s7.globals.rawHeap s7.locals.drv with rx_head := Ptr.null } : C_uart_driver) :=
      hVal_heapUpdate_same _ _ _ hb7
    have h7v : hVal s7.globals.rawHeap s7.locals.drv =
        ({ hVal s6.globals.rawHeap s6.locals.drv with error_count := 0 } : C_uart_driver) :=
      hVal_heapUpdate_same _ _ _ hb6
    have h6v : hVal s6.globals.rawHeap s6.locals.drv =
        ({ hVal s5.globals.rawHeap s5.locals.drv with rx_count := 0 } : C_uart_driver) :=
      hVal_heapUpdate_same _ _ _ hb5
    have h5v : hVal s5.globals.rawHeap s5.locals.drv =
        ({ hVal s4.globals.rawHeap s4.locals.drv with tx_count := 0 } : C_uart_driver) :=
      hVal_heapUpdate_same _ _ _ hb4
    have h4v : hVal s4.globals.rawHeap s4.locals.drv =
        ({ hVal s3.globals.rawHeap s3.locals.drv with clock_freq := s3.locals.clock_freq } : C_uart_driver) :=
      hVal_heapUpdate_same _ _ _ hb3
    have h3v : hVal s3.globals.rawHeap s3.locals.drv =
        ({ hVal s2.globals.rawHeap s2.locals.drv with baud_rate := 0 } : C_uart_driver) :=
      hVal_heapUpdate_same _ _ _ hb2
    have h2v : hVal s2.globals.rawHeap s2.locals.drv =
        ({ hVal s1.globals.rawHeap s1.locals.drv with state := 0 } : C_uart_driver) :=
      hVal_heapUpdate_same _ _ _ hb1
    have h1v : hVal s1.globals.rawHeap s1.locals.drv =
        ({ hVal s.globals.rawHeap s.locals.drv with regs := s.locals.regs } : C_uart_driver) :=
      hVal_heapUpdate_same _ _ _ hb
    -- ret__val = 0 and driver fields
    refine ⟨uart_f_ret_ret_val s11, ?_⟩
    -- s_final heap = s11 heap, s_final drv = s11 drv (f_ret only changes locals.ret__val)
    rw [show s_final.globals.rawHeap = s11.globals.rawHeap from
      congrArg (fun g => g.rawHeap) (uart_f_ret_globals s11)]
    rw [show s_final.locals.drv = s11.locals.drv from uart_f_ret_drv s11]
    rw [h11v, h10v, h9v, h8v, h7v, h6v, h5v, h4v, h3v, h2v, h1v]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

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
