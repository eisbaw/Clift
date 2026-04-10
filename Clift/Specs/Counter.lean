-- Counter: Reusable abstract specification for a bounded counter
--
-- Abstract state: value + bounds.
-- Operations: increment, decrement, reset, getValue, setValue.
-- Key properties: value always within bounds, inc/dec inverse,
--                 reset returns to zero.
--
-- To instantiate: define simulation relation from C struct to CounterState.

import Clift.Lifting.AbstractSpec

namespace Specs.Counter

/-- Abstract state for a bounded counter. -/
structure CounterState where
  /-- Current counter value -/
  value : Nat
  /-- Minimum allowed value (usually 0) -/
  minValue : Nat
  /-- Maximum allowed value -/
  maxValue : Nat
  deriving Repr

/-- Operations on the counter. -/
inductive CounterOp where
  | increment
  | decrement
  | reset
  | getValue
  | setValue (v : Nat)

/-- Abstract specification for a bounded counter. -/
def counterSpec : AbstractSpec CounterState CounterOp where
  init := fun s => s.value = s.minValue ∧ s.minValue ≤ s.maxValue
  opSpec := fun op => match op with
    | .increment => {
        pre := fun s => s.value < s.maxValue
        post := fun s s' => s'.value = s.value + 1 ∧
                            s'.minValue = s.minValue ∧ s'.maxValue = s.maxValue
      }
    | .decrement => {
        pre := fun s => s.value > s.minValue
        post := fun s s' => s'.value = s.value - 1 ∧
                            s'.minValue = s.minValue ∧ s'.maxValue = s.maxValue
      }
    | .reset => {
        pre := fun _ => True
        post := fun s s' => s'.value = s.minValue ∧
                            s'.minValue = s.minValue ∧ s'.maxValue = s.maxValue
      }
    | .getValue => {
        pre := fun _ => True
        post := fun s s' => s' = s
      }
    | .setValue v => {
        pre := fun s => s.minValue ≤ v ∧ v ≤ s.maxValue
        post := fun s s' => s'.value = v ∧
                            s'.minValue = s.minValue ∧ s'.maxValue = s.maxValue
      }
  inv := fun s => s.minValue ≤ s.value ∧ s.value ≤ s.maxValue ∧ s.minValue ≤ s.maxValue

/-! # Key Properties -/

/-- Increment followed by decrement is identity on value. -/
theorem inc_dec_inverse (s s1 s2 : CounterState)
    (h_inc : (counterSpec.opSpec .increment).post s s1)
    (h_dec : (counterSpec.opSpec .decrement).post s1 s2) :
    s2.value = s.value := by
  obtain ⟨h1, _, _⟩ := h_inc
  obtain ⟨h2, _, _⟩ := h_dec
  omega

/-- Decrement followed by increment is identity on value
    (requires value > minValue so Nat subtraction doesn't bottom out). -/
theorem dec_inc_inverse (s s1 s2 : CounterState)
    (h_pre : s.value > s.minValue)
    (h_dec : (counterSpec.opSpec .decrement).post s s1)
    (h_inc : (counterSpec.opSpec .increment).post s1 s2) :
    s2.value = s.value := by
  obtain ⟨h1, _, _⟩ := h_dec
  obtain ⟨h2, _, _⟩ := h_inc
  omega

/-- Value is always within bounds (invariant). -/
theorem value_bounded (s : CounterState) (h_inv : counterSpec.inv s) :
    s.minValue ≤ s.value ∧ s.value ≤ s.maxValue :=
  ⟨h_inv.1, h_inv.2.1⟩

/-- Invariant preserved by increment. -/
theorem inv_increment (s s' : CounterState)
    (h_inv : counterSpec.inv s)
    (h_pre : (counterSpec.opSpec .increment).pre s)
    (h_post : (counterSpec.opSpec .increment).post s s') :
    counterSpec.inv s' := by
  obtain ⟨h_min, h_max, h_bound⟩ := h_inv
  obtain ⟨h_val, h_min', h_max'⟩ := h_post
  simp only [counterSpec] at h_pre
  exact ⟨by omega, by omega, by omega⟩

/-- Invariant preserved by decrement. -/
theorem inv_decrement (s s' : CounterState)
    (h_inv : counterSpec.inv s)
    (h_pre : (counterSpec.opSpec .decrement).pre s)
    (h_post : (counterSpec.opSpec .decrement).post s s') :
    counterSpec.inv s' := by
  obtain ⟨h_min, h_max, h_bound⟩ := h_inv
  obtain ⟨h_val, h_min', h_max'⟩ := h_post
  simp only [counterSpec] at h_pre
  exact ⟨by omega, by omega, by omega⟩

/-- Invariant preserved by reset. -/
theorem inv_reset (s s' : CounterState)
    (h_inv : counterSpec.inv s)
    (h_post : (counterSpec.opSpec .reset).post s s') :
    counterSpec.inv s' := by
  obtain ⟨_, _, h_bound⟩ := h_inv
  obtain ⟨h_val, h_min', h_max'⟩ := h_post
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- After reset, value equals minValue. -/
theorem reset_to_min (s s' : CounterState)
    (h_post : (counterSpec.opSpec .reset).post s s') :
    s'.value = s'.minValue := by
  obtain ⟨h_val, h_min', _⟩ := h_post
  omega

/-! # Instantiation Guide

To verify a concrete C counter:

```
-- Simulation relation: map C uint32_t fields to CounterState
def counterSim (cs : MyCounter.ProgramState) (as : Specs.Counter.CounterState) : Prop :=
  (hVal cs.globals.rawHeap cs.locals.counter_ptr).value.toNat = as.value /\
  (hVal cs.globals.rawHeap cs.locals.counter_ptr).max_val.toNat = as.maxValue /\
  as.minValue = 0

-- Then prove opRefinement for each operation.
-- inc_dec_inverse, value_bounded, etc. transfer automatically.
```
-/

end Specs.Counter
