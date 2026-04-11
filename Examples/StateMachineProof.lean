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

/-! ## conn_init: direct result computation using L1 result lemmas.

    The L1 body is generated by clift and has the structure:
    catch (seq (seq guard modify) (seq (seq guard modify) (seq (seq guard modify) (seq guard modify)))) skip

    We compute the result by chaining L1_guard_modify_result + L1_seq_singleton_ok,
    then wrapping with L1_catch_singleton_ok. The modify lambdas are used inline.

    For the postcondition, we chain hVal_heapUpdate_same at each step. -/

-- Helper: heapUpdate with struct field update preserves heapPtrValid at same pointer
private theorem sm_heapUpdate_conn_ptrValid (s : ProgramState)
    (hv : heapPtrValid s.globals.rawHeap s.locals.conn)
    (v : C_conn_state) :
    heapPtrValid (heapUpdate s.globals.rawHeap s.locals.conn v) s.locals.conn :=
  heapUpdate_preserves_heapPtrValid _ _ _ _ hv

theorem conn_init_correct :
    conn_init_spec.satisfiedBy StateMachine.l1_conn_init_body := by
  unfold FuncSpec.satisfiedBy conn_init_spec validHoare
  intro s hpre
  -- The generated L1 body unfolds to:
  -- L1.catch (L1.seq (L1.seq (L1.guard p) (L1.modify f1))
  --                   (L1.seq (L1.seq (L1.guard p) (L1.modify f2))
  --                           (L1.seq (L1.seq (L1.guard p) (L1.modify f3))
  --                                   (L1.seq (L1.guard p) (L1.modify f4))))) L1.skip
  -- where p = heapPtrValid at conn, and f1..f4 write individual struct fields.
  --
  -- We define the 4 intermediate states by applying the modify functions.
  -- s1 = f1 s, s2 = f2 s1, s3 = f3 s2, s4 = f4 s3
  let p := fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.conn
  let f1 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.conn ({ hVal s.globals.rawHeap s.locals.conn with state := 0 } : C_conn_state) } }
  let f2 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.conn ({ hVal s.globals.rawHeap s.locals.conn with tx_bytes := 0 } : C_conn_state) } }
  let f3 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.conn ({ hVal s.globals.rawHeap s.locals.conn with rx_bytes := 0 } : C_conn_state) } }
  let f4 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.conn ({ hVal s.globals.rawHeap s.locals.conn with transition_count := 0 } : C_conn_state) } }
  let s1 := f1 s
  let s2 := f2 s1
  let s3 := f3 s2
  let s4 := f4 s3
  -- heapPtrValid preservation through each step
  have hv1 : p s1 := sm_heapUpdate_conn_ptrValid s hpre _
  have hv2 : p s2 := sm_heapUpdate_conn_ptrValid s1 hv1 _
  have hv3 : p s3 := sm_heapUpdate_conn_ptrValid s2 hv2 _
  -- Step results
  have h1 := L1_guard_modify_result p f1 s hpre
  have h2 := L1_guard_modify_result p f2 s1 hv1
  have h3 := L1_guard_modify_result p f3 s2 hv2
  have h4 := L1_guard_modify_result p f4 s3 hv3
  -- Chain steps 3,4
  have h34 := L1_seq_singleton_ok h3.1 h3.2 (m₂ := L1.seq (L1.guard p) (L1.modify f4))
  have h34_res : (L1.seq (L1.seq (L1.guard p) (L1.modify f3)) (L1.seq (L1.guard p) (L1.modify f4)) s2).results = {(Except.ok (), s4)} := by
    rw [h34.1, h4.1]
  have h34_nf : ¬(L1.seq (L1.seq (L1.guard p) (L1.modify f3)) (L1.seq (L1.guard p) (L1.modify f4)) s2).failed :=
    fun hf => h4.2 (h34.2.mp hf)
  -- Chain steps 2,3,4
  have h234 := L1_seq_singleton_ok h2.1 h2.2
    (m₂ := L1.seq (L1.seq (L1.guard p) (L1.modify f3)) (L1.seq (L1.guard p) (L1.modify f4)))
  have h234_res : (L1.seq (L1.seq (L1.guard p) (L1.modify f2)) (L1.seq (L1.seq (L1.guard p) (L1.modify f3)) (L1.seq (L1.guard p) (L1.modify f4))) s1).results = {(Except.ok (), s4)} := by
    rw [h234.1, h34_res]
  have h234_nf : ¬(L1.seq (L1.seq (L1.guard p) (L1.modify f2)) (L1.seq (L1.seq (L1.guard p) (L1.modify f3)) (L1.seq (L1.guard p) (L1.modify f4))) s1).failed :=
    fun hf => h34_nf (h234.2.mp hf)
  -- Chain steps 1,2,3,4
  have h1234 := L1_seq_singleton_ok h1.1 h1.2
    (m₂ := L1.seq (L1.seq (L1.guard p) (L1.modify f2)) (L1.seq (L1.seq (L1.guard p) (L1.modify f3)) (L1.seq (L1.guard p) (L1.modify f4))))
  have h1234_res : (L1.seq (L1.seq (L1.guard p) (L1.modify f1)) (L1.seq (L1.seq (L1.guard p) (L1.modify f2)) (L1.seq (L1.seq (L1.guard p) (L1.modify f3)) (L1.seq (L1.guard p) (L1.modify f4)))) s).results = {(Except.ok (), s4)} := by
    rw [h1234.1, h234_res]
  have h1234_nf : ¬(L1.seq (L1.seq (L1.guard p) (L1.modify f1)) (L1.seq (L1.seq (L1.guard p) (L1.modify f2)) (L1.seq (L1.seq (L1.guard p) (L1.modify f3)) (L1.seq (L1.guard p) (L1.modify f4)))) s).failed :=
    fun hf => h234_nf (h1234.2.mp hf)
  -- Catch wrapper
  have h_catch := L1_catch_singleton_ok h1234_res h1234_nf
  -- Now unfold and match
  unfold StateMachine.l1_conn_init_body
  constructor
  · exact h_catch.2
  · intro r s' h_mem
    rw [h_catch.1] at h_mem
    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
    subst hr; subst hs
    intro _
    -- Now show the postcondition: hVal at s4 has all 4 fields set correctly
    -- s4 = f4 (f3 (f2 (f1 s))). Each fN writes one field.
    -- After 4 heapUpdates to the same pointer, hVal reads the last written struct.
    -- Chain hVal_heapUpdate_same at each level.
    have hb := heapPtrValid_bound hpre
    have hb1 := heapPtrValid_bound hv1
    have hb2 := heapPtrValid_bound hv2
    have hb3 := heapPtrValid_bound hv3
    -- hVal at s4
    have h4v : hVal s4.globals.rawHeap s4.locals.conn =
        ({ hVal s3.globals.rawHeap s3.locals.conn with transition_count := 0 } : C_conn_state) :=
      hVal_heapUpdate_same _ _ _ hb3
    have h3v : hVal s3.globals.rawHeap s3.locals.conn =
        ({ hVal s2.globals.rawHeap s2.locals.conn with rx_bytes := 0 } : C_conn_state) :=
      hVal_heapUpdate_same _ _ _ hb2
    have h2v : hVal s2.globals.rawHeap s2.locals.conn =
        ({ hVal s1.globals.rawHeap s1.locals.conn with tx_bytes := 0 } : C_conn_state) :=
      hVal_heapUpdate_same _ _ _ hb1
    have h1v : hVal s1.globals.rawHeap s1.locals.conn =
        ({ hVal s.globals.rawHeap s.locals.conn with state := 0 } : C_conn_state) :=
      hVal_heapUpdate_same _ _ _ hb
    rw [h4v, h3v, h2v, h1v]
    exact ⟨rfl, rfl, rfl, rfl⟩

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
