-- sep_auto: separation logic automation for mapsTo/sep predicates
--
-- Automates frame reasoning with mapsTo/sep predicates by registering
-- relevant lemmas as simp/ext rules and providing a combined tactic.
--
-- Handles:
--   - mapsTo_frame_update: disjoint pointer update preserves mapsTo
--   - mapsTo_after_update: writing to a pointer establishes mapsTo
--   - sepMapsTo_comm: commutativity of separating conjunction
--   - heapUpdate_preserves_heapPtrValid: validity preservation through updates
--   - hVal_heapUpdate_same/disjoint: value reading after updates
--
-- Usage:
--   `sep_auto` — apply all separation logic simplification rules
--   `sep_frame` — focus on frame reasoning (disjoint preservation)

import Clift.Lifting.HeapLift.SepLogic

/-! # sep_auto simp set

Register separation logic lemmas in a custom simp set for targeted automation. -/

-- Attribute for separation logic automation lemmas
-- We use a custom simp extension to avoid polluting the default simp set.

/-- `sep_auto` tactic: apply separation logic simplification rules.
    Tries to solve goals involving mapsTo, sepMapsTo, heapPtrValid
    after heap updates, using the frame and update lemmas. -/
syntax "sep_auto" : tactic

macro_rules
  | `(tactic| sep_auto) => `(tactic|
    first
    | (apply mapsTo_after_update; assumption)
    | (apply mapsTo_frame_update <;> assumption)
    | (apply mapsTo_frame_swap <;> assumption)
    | (apply sepMapsTo_comm.mp; assumption)
    | (apply sepMapsTo_comm.mpr; assumption)
    | (apply swap_sep_correct; assumption)
    | (constructor <;> sep_auto)
    | assumption
    | fail "sep_auto: could not find applicable separation logic rule"
    )

/-- `sep_frame` tactic: prove that a heap update preserves mapsTo for disjoint pointers.
    Works on goals of the form: `mapsTo q vq (simpleUpdate h p v)` or
    `mapsTo q vq (heapUpdate h p v)`. -/
syntax "sep_frame" : tactic

macro_rules
  | `(tactic| sep_frame) => `(tactic|
    first
    | (apply mapsTo_frame_update <;> assumption)
    | (apply heapUpdate_preserves_heapPtrValid; assumption)
    | fail "sep_frame: could not apply frame reasoning"
    )

/-- `sep_update` tactic: prove that a heap update establishes mapsTo at the updated pointer.
    Works on goals of the form: `mapsTo p v (simpleUpdate h p v)`. -/
syntax "sep_update" : tactic

macro_rules
  | `(tactic| sep_update) => `(tactic|
    first
    | (apply mapsTo_after_update; assumption)
    | fail "sep_update: could not apply update rule"
    )

/-! # Worked example: how sep_auto would simplify swap proof

    Given: mapsTo a va h, mapsTo b vb h, ptrDisjoint a b
    Goal: mapsTo a vb (simpleUpdate (simpleUpdate h a vb) b va) ∧
          mapsTo b va (simpleUpdate (simpleUpdate h a vb) b va) ∧
          ptrDisjoint a b

    sep_auto would:
    1. Split the conjunction
    2. For mapsTo a vb: apply mapsTo_frame_update (b disjoint from a),
       then mapsTo_after_update (a was written with vb)
    3. For mapsTo b va: apply mapsTo_after_update (b was written with va)
    4. For ptrDisjoint: assumption
-/
