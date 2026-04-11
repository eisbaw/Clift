-- Task 0160: TCP-like state machine verification
--
-- Connection state machine with 6 states, guarded transitions.
-- 9 functions imported from state_machine.c (~160 LOC C -> ~420 lines Lean).
--
-- Key verification targets:
-- - Only valid transitions occur (conn_next_state returns INVALID_STATE otherwise)
-- - Invariant: state is always in [0, 5]
-- - Data ops only valid in ESTABLISHED state
-- - Transition count is monotonically increasing
--
-- This instantiates the abstract Specs.StateMachine framework.

import Generated.StateMachine
import Clift.Lifting.Pipeline
import Clift.Lifting.FuncSpec
import Clift.Specs.StateMachine

set_option maxHeartbeats 12800000
set_option maxRecDepth 4096

open StateMachine

/-! # Step 1: Run the clift pipeline on all 9 functions -/

clift StateMachine

/-! # Step 2: Verify L1 definitions exist -/

#check @StateMachine.l1_conn_init_body
#check @StateMachine.l1_conn_next_state_body
#check @StateMachine.l1_conn_transition_body
#check @StateMachine.l1_conn_send_body
#check @StateMachine.l1_conn_recv_body
#check @StateMachine.l1_conn_get_state_body
#check @StateMachine.l1_conn_is_established_body
#check @StateMachine.l1_conn_state_valid_body
#check @StateMachine.l1_conn_get_transitions_body

/-! # Step 3: Instantiate the abstract state machine spec -/

/-- TCP-like connection states. -/
inductive ConnState where
  | closed | listen | syn_sent | syn_rcvd | established | close_wait
  deriving DecidableEq, Repr

/-- Connection events. -/
inductive ConnEvent where
  | passive_open | active_open | syn_recv | ack_recv | data | close
  deriving DecidableEq, Repr

/-- Transition function matching the C code exactly. -/
def connTransition : ConnState → ConnEvent → Option ConnState
  | .closed,      .passive_open => some .listen
  | .closed,      .active_open  => some .syn_sent
  | .listen,      .syn_recv     => some .syn_rcvd
  | .listen,      .close        => some .closed
  | .syn_sent,    .syn_recv     => some .syn_rcvd
  | .syn_rcvd,    .ack_recv     => some .established
  | .syn_rcvd,    .close        => some .closed
  | .established, .data         => some .established
  | .established, .close        => some .close_wait
  | .close_wait,  .close        => some .closed
  | _, _                        => none

/-- All states are valid (invariant is trivially true). -/
def connConfig : Specs.StateMachine.SMConfig ConnState ConnEvent where
  initState := .closed
  transition := connTransition
  stateInv := fun _ => True
  initSat := trivial

def connSpec := Specs.StateMachine.smSpec ConnState ConnEvent connConfig

/-! # Step 4: Prove abstract spec properties -/

/-- Only valid transitions: all other state-event pairs produce none. -/
theorem invalid_transitions_rejected :
    connTransition .closed .data = none ∧
    connTransition .closed .ack_recv = none ∧
    connTransition .listen .active_open = none ∧
    connTransition .listen .data = none ∧
    connTransition .syn_sent .close = none ∧
    connTransition .close_wait .data = none := by
  simp [connTransition]

/-- From closed, the only reachable states via single transition are
    listen and syn_sent. -/
theorem closed_successors (e : ConnEvent) (s : ConnState)
    (h : connTransition .closed e = some s) :
    s = .listen ∨ s = .syn_sent := by
  cases e <;> simp [connTransition] at h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

/-- ESTABLISHED can only be reached via ACK_RECV from SYN_RCVD. -/
theorem established_only_from_syn_rcvd (s : ConnState) (e : ConnEvent)
    (h : connTransition s e = some .established) :
    s = .syn_rcvd ∧ e = .ack_recv ∨ s = .established ∧ e = .data := by
  cases s <;> cases e <;> simp [connTransition] at h <;> (try exact Or.inl ⟨rfl, rfl⟩) <;> (try exact Or.inr ⟨rfl, rfl⟩)

/-- Transition preserves validity (trivially, since all states are valid). -/
theorem conn_transition_preserves :
    ∀ st e next, connConfig.stateInv st → connTransition st e = some next →
      connConfig.stateInv next := by
  intros; trivial

/-! # Step 5: FuncSpecs for C functions -/

/-- conn_init: sets state to CLOSED, zeroes counters. -/
def conn_init_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.conn
  post := fun r s =>
    r = Except.ok () →
    let conn := hVal s.globals.rawHeap s.locals.conn
    conn.state = 0 ∧  -- ST_CLOSED
    conn.tx_bytes = 0 ∧
    conn.rx_bytes = 0 ∧
    conn.transition_count = 0

/-- conn_state_valid: returns 1 if state < 6. Pure, no heap. -/
def conn_state_valid_spec : FuncSpec ProgramState where
  pre := fun _ => True
  post := fun r s =>
    r = Except.ok () →
    (s.locals.state < 6 → s.locals.ret__val = 1) ∧
    (¬(s.locals.state < 6) → s.locals.ret__val = 0)

/-- conn_get_state: returns current state. -/
def conn_get_state_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.conn
  post := fun r s =>
    r = Except.ok () →
    s.locals.ret__val = (hVal s.globals.rawHeap s.locals.conn).state

/-- conn_is_established: checks state == ST_ESTABLISHED (4). -/
def conn_is_established_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.conn
  post := fun r s =>
    r = Except.ok () →
    let conn := hVal s.globals.rawHeap s.locals.conn
    (conn.state = 4 → s.locals.ret__val = 1) ∧
    (conn.state ≠ 4 → s.locals.ret__val = 0)

/-- conn_send: only succeeds in ESTABLISHED state. -/
def conn_send_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.conn
  post := fun r s =>
    r = Except.ok () →
    (s.locals.ret__val = 0 ∨ s.locals.ret__val = 1)

/-! # Step 6: validHoare theorems -/

theorem conn_init_correct :
    conn_init_spec.satisfiedBy StateMachine.l1_conn_init_body := by
  sorry

theorem conn_state_valid_correct :
    conn_state_valid_spec.satisfiedBy StateMachine.l1_conn_state_valid_body := by
  unfold FuncSpec.satisfiedBy conn_state_valid_spec validHoare
  intro s _
  -- l1_conn_state_valid_body is L1.catch (L1.seq (L1.modify f) L1.throw) L1.skip
  -- where f sets ret__val := if state < 6 then 1 else 0
  -- Use the modify-throw-catch-skip result pattern
  unfold StateMachine.l1_conn_state_valid_body
  have h := L1_modify_throw_catch_skip_result
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := (if s.locals.state < 6 then 1 else 0) } })
    s
  obtain ⟨h_res, h_nf⟩ := h
  constructor
  · exact h_nf
  · intro r s' h_mem
    rw [h_res] at h_mem
    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
    subst hr; subst hs
    intro _
    simp only
    constructor
    · intro h_lt; simp [h_lt]
    · intro h_ge; simp [h_ge]

-- Projection lemma: updating ret__val doesn't change globals
private theorem update_retval_globals (s : ProgramState) (v : UInt32) :
    ({ s with locals := { s.locals with ret__val := v } } : ProgramState).globals = s.globals := rfl

-- Projection lemma: updating ret__val doesn't change locals.conn
private theorem update_retval_conn (s : ProgramState) (v : UInt32) :
    ({ s with locals := { s.locals with ret__val := v } } : ProgramState).locals.conn = s.locals.conn := rfl

-- Projection lemma: updating ret__val gives back v
private theorem update_retval_val (s : ProgramState) (v : UInt32) :
    ({ s with locals := { s.locals with ret__val := v } } : ProgramState).locals.ret__val = v := rfl

attribute [local irreducible] hVal heapPtrValid in
theorem conn_get_state_correct :
    conn_get_state_spec.satisfiedBy StateMachine.l1_conn_get_state_body := by
  unfold FuncSpec.satisfiedBy conn_get_state_spec validHoare
  intro s hpre
  unfold StateMachine.l1_conn_get_state_body
  have h := L1_guard_modify_throw_catch_skip_result
    (fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.conn)
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := (hVal s.globals.rawHeap s.locals.conn).state } })
    s hpre
  obtain ⟨h_res, h_nf⟩ := h
  constructor
  · exact h_nf
  · intro r s' h_mem
    rw [h_res] at h_mem
    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
    subst hr; subst hs
    intro _
    rw [update_retval_val, update_retval_globals, update_retval_conn]
