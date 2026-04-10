-- StateMachine: Reusable abstract specification for a generic state machine
--
-- Abstract state: current state + event history.
-- Operations: transition (event-driven), reset, getState.
-- Key properties: transitions respect allowed edges, invariant preservation,
--                 no invalid state reachable.
--
-- To instantiate: define your states, events, transition function, and invariant.

import Clift.Lifting.AbstractSpec

namespace Specs.StateMachine

/-- A generic state machine specification.
    S = state type (e.g., an inductive type for protocol states)
    E = event type (e.g., input commands) -/
structure SMConfig (S E : Type) where
  /-- Initial state -/
  initState : S
  /-- Transition function: given current state and event, produce next state.
      Returns none if the transition is invalid (not allowed). -/
  transition : S → E → Option S
  /-- State invariant: must hold for every reachable state -/
  stateInv : S → Prop
  /-- The initial state satisfies the invariant -/
  initSat : stateInv initState

/-- Abstract state for the state machine. -/
structure SMState (S E : Type) where
  /-- Current state -/
  current : S
  /-- Number of transitions performed -/
  transitionCount : Nat
  deriving Repr

/-- Operations on the state machine. -/
inductive SMOp (E : Type) where
  | transition (event : E)
  | reset
  | getState

/-- Build an AbstractSpec from an SMConfig. -/
def smSpec (S E : Type) (cfg : SMConfig S E) : AbstractSpec (SMState S E) (SMOp E) where
  init := fun s => s.current = cfg.initState ∧ s.transitionCount = 0
  opSpec := fun op => match op with
    | .transition event => {
        pre := fun s => (cfg.transition s.current event).isSome
        post := fun s s' =>
          ∃ next, cfg.transition s.current event = some next ∧
          s'.current = next ∧
          s'.transitionCount = s.transitionCount + 1
      }
    | .reset => {
        pre := fun _ => True
        post := fun _ s' => s'.current = cfg.initState ∧ s'.transitionCount = 0
      }
    | .getState => {
        pre := fun _ => True
        post := fun s s' => s' = s
      }
  inv := fun s => cfg.stateInv s.current

/-! # Key Properties -/

/-- After reset, the state machine is in its initial state. -/
theorem reset_to_init {S E : Type} (cfg : SMConfig S E) (s s' : SMState S E)
    (h_post : ((smSpec S E cfg).opSpec .reset).post s s') :
    s'.current = cfg.initState := by
  obtain ⟨h, _⟩ := h_post; exact h

/-- Valid transitions preserve the state invariant (if the config's
    transition function preserves it). -/
theorem transition_preserves_inv {S E : Type} (cfg : SMConfig S E)
    (s s' : SMState S E) (event : E)
    (h_inv : (smSpec S E cfg).inv s)
    (h_post : ((smSpec S E cfg).opSpec (.transition event)).post s s')
    (h_trans_pres : ∀ st e next, cfg.stateInv st → cfg.transition st e = some next → cfg.stateInv next) :
    (smSpec S E cfg).inv s' := by
  obtain ⟨next, h_trans, h_curr, _⟩ := h_post
  show cfg.stateInv s'.current
  rw [h_curr]
  exact h_trans_pres s.current event next h_inv h_trans

/-- Transition count is monotonically increasing. -/
theorem transition_count_monotone {S E : Type} (cfg : SMConfig S E)
    (s s' : SMState S E) (event : E)
    (h_post : ((smSpec S E cfg).opSpec (.transition event)).post s s') :
    s'.transitionCount = s.transitionCount + 1 := by
  obtain ⟨_, _, _, h⟩ := h_post; exact h

/-! # Example: Simple Protocol State Machine

A three-state protocol: IDLE -> CONNECTING -> CONNECTED -> IDLE

```
-- Define states
inductive ProtoState where
  | idle | connecting | connected
  deriving DecidableEq, Repr

-- Define events
inductive ProtoEvent where
  | connect | established | disconnect | timeout
  deriving Repr

-- Define transitions
def protoTransition : ProtoState -> ProtoEvent -> Option ProtoState
  | .idle, .connect => some .connecting
  | .connecting, .established => some .connected
  | .connecting, .timeout => some .idle
  | .connected, .disconnect => some .idle
  | _, _ => none  -- all other transitions invalid

-- Define config
def protoConfig : SMConfig ProtoState ProtoEvent where
  initState := .idle
  transition := protoTransition
  stateInv := fun _ => True  -- all states valid
  initSat := trivial

-- Build the spec
def protoSpec := smSpec ProtoState ProtoEvent protoConfig
```
-/

/-! # Instantiation Guide

To verify a concrete C state machine:

```
-- 1. Define your states and events as inductive types
-- 2. Define the transition function
-- 3. Create an SMConfig with your invariant
-- 4. Use smSpec to get the AbstractSpec
-- 5. Define simulation relation: C struct fields -> SMState
-- 6. Prove opRefinement for each operation
-- 7. transition_preserves_inv transfers to C via refinement
```
-/

end Specs.StateMachine
