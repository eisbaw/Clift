-- BoundedMap: Reusable abstract specification for a bounded key-value map
--
-- Abstract state: partial function from keys to values with capacity.
-- Operations: get, put, remove, contains, size, clear.
-- Key properties: put/get consistency, remove/get consistency, bounded size.
--
-- Useful for: hash tables, lookup tables, configuration stores.

import Clift.Lifting.AbstractSpec

namespace Specs.BoundedMap

/-- Abstract state for a bounded map from K to V. -/
structure MapState (K V : Type) where
  /-- The map contents -/
  store : K → Option V
  /-- Number of entries -/
  count : Nat
  /-- Maximum capacity -/
  capacity : Nat
  -- Note: no Repr because (K -> Option V) has no generic Repr instance

/-- Operations on the map. -/
inductive MapOp (K V : Type) where
  | get (k : K)
  | put (k : K) (v : V)
  | remove (k : K)
  | contains (k : K)
  | size
  | clear

/-- Abstract specification for a bounded key-value map. -/
def mapSpec (K V : Type) : AbstractSpec (MapState K V) (MapOp K V) where
  init := fun s => s.store = (fun _ => none) ∧ s.count = 0 ∧ s.capacity > 0
  opSpec := fun op => match op with
    | .get _k => {
        pre := fun _ => True
        post := fun s s' => s'.store = s.store ∧ s'.count = s.count ∧
                            s'.capacity = s.capacity
      }
    | .put k v => {
        pre := fun s => s.store k ≠ none ∨ s.count < s.capacity
        post := fun s s' =>
          s'.store k = some v ∧
          (∀ k', k' ≠ k → s'.store k' = s.store k') ∧
          s'.capacity = s.capacity ∧
          -- count increases by 1 if key was new, stays same if overwrite
          (s.store k = none → s'.count = s.count + 1) ∧
          (s.store k ≠ none → s'.count = s.count)
      }
    | .remove k => {
        pre := fun _ => True
        post := fun s s' =>
          s'.store k = none ∧
          (∀ k', k' ≠ k → s'.store k' = s.store k') ∧
          s'.capacity = s.capacity ∧
          (s.store k ≠ none → s'.count = s.count - 1) ∧
          (s.store k = none → s'.count = s.count)
      }
    | .contains _k => {
        pre := fun _ => True
        post := fun s s' => s' = s
      }
    | .size => {
        pre := fun _ => True
        post := fun s s' => s' = s
      }
    | .clear => {
        pre := fun _ => True
        post := fun _ s' => s'.store = (fun _ => none) ∧ s'.count = 0 ∧ s'.capacity > 0
      }
  inv := fun s => s.count ≤ s.capacity ∧ s.capacity > 0

/-! # Key Properties -/

/-- Put then get returns the put value. -/
theorem put_get {K V : Type} [DecidableEq K]
    (s : MapState K V) (k : K) (v : V) (s' : MapState K V)
    (h_put : ((mapSpec K V).opSpec (.put k v)).post s s') :
    s'.store k = some v := h_put.1

/-- Put preserves other keys. -/
theorem put_other {K V : Type} [DecidableEq K]
    (s : MapState K V) (k k' : K) (v : V) (s' : MapState K V)
    (h_put : ((mapSpec K V).opSpec (.put k v)).post s s')
    (h_neq : k' ≠ k) :
    s'.store k' = s.store k' := h_put.2.1 k' h_neq

/-- Remove then get returns none. -/
theorem remove_get {K V : Type}
    (s : MapState K V) (k : K) (s' : MapState K V)
    (h_remove : ((mapSpec K V).opSpec (.remove k)).post s s') :
    s'.store k = none := h_remove.1

/-- Remove preserves other keys. -/
theorem remove_other {K V : Type} [DecidableEq K]
    (s : MapState K V) (k k' : K) (s' : MapState K V)
    (h_remove : ((mapSpec K V).opSpec (.remove k)).post s s')
    (h_neq : k' ≠ k) :
    s'.store k' = s.store k' := h_remove.2.1 k' h_neq

/-- Clear then get returns none for any key. -/
theorem clear_get {K V : Type}
    (s s' : MapState K V) (k : K)
    (h_clear : ((mapSpec K V).opSpec .clear).post s s') :
    s'.store k = none := by
  have h := h_clear.1
  show s'.store k = none
  rw [h]

/-! # Instantiation Guide

To verify a concrete C hash table or lookup table:

```
-- Simulation relation: C array/struct -> MapState
def mapSim (cs : MyMap.ProgramState) (as : Specs.BoundedMap.MapState Nat Nat) : Prop :=
  -- Map C array entries to abstract store function
  -- Map C count field to as.count
  -- Map C capacity constant to as.capacity

-- Prove opRefinement for get, put, remove, etc.
-- put_get, remove_get properties transfer automatically.
```
-/

end Specs.BoundedMap
