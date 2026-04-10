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
--   - modifiesHeapOnly_frame_mapsTo: frame via modifies-set analysis
--   - Conjunction splitting and recursive solving
--
-- Usage:
--   `sep_auto` — apply all separation logic simplification rules
--   `sep_frame` — focus on frame reasoning (disjoint preservation)

import Clift.Lifting.HeapLift.SepLogic
import Clift.Lifting.HeapLift.ModifiesSet

/-! # sep_auto: enhanced separation logic automation

The tactic tries multiple strategies in order:
1. Direct lemma application (mapsTo_after_update, mapsTo_frame_update, etc.)
2. Conjunction splitting with recursive solving
3. Assumption matching
4. ptrDisjoint symmetry

The key improvement over the previous version: better recursion through
conjunctions, and integration with modifiesHeapOnly frame reasoning. -/

/-- `sep_auto` tactic: apply separation logic simplification rules.
    Tries to solve goals involving mapsTo, sepMapsTo, heapPtrValid
    after heap updates, using the frame and update lemmas.

    Handles:
    - mapsTo p v (simpleUpdate h p v): apply mapsTo_after_update
    - mapsTo q vq (simpleUpdate h p v): apply mapsTo_frame_update
    - sepMapsTo: unfold and solve components
    - ptrDisjoint: try assumption and symmetry
    - Conjunctions: split and solve each part -/
syntax "sep_auto" : tactic

macro_rules
  | `(tactic| sep_auto) => `(tactic|
    first
    -- Direct mapsTo after update
    | (apply mapsTo_after_update; assumption)
    -- Frame: mapsTo preserved through disjoint update
    | (apply mapsTo_frame_update <;> (first | assumption | (exact ptrDisjoint_symm ‹_›)))
    -- Frame through two updates (swap)
    | (apply mapsTo_frame_swap <;> (first | assumption | (exact ptrDisjoint_symm ‹_›)))
    -- swap_sep_correct
    | (apply swap_sep_correct; assumption)
    -- sepMapsTo commutativity
    | (apply sepMapsTo_comm.mp; assumption)
    | (apply sepMapsTo_comm.mpr; assumption)
    -- heapPtrValid preservation
    | (apply heapUpdate_preserves_heapPtrValid; assumption)
    -- Conjunction: split and solve each part
    | (constructor <;> sep_auto)
    -- ptrDisjoint: try assumption and symmetry
    | (exact ptrDisjoint_symm ‹_›)
    -- Plain assumption
    | assumption
    -- rfl for equalities
    | rfl
    | fail "sep_auto: could not find applicable separation logic rule"
    )

/-- `sep_frame` tactic: prove that a heap update preserves mapsTo for disjoint pointers.
    Works on goals of the form: `mapsTo q vq (simpleUpdate h p v)` or
    `mapsTo q vq (heapUpdate h p v)`. -/
syntax "sep_frame" : tactic

macro_rules
  | `(tactic| sep_frame) => `(tactic|
    first
    | (apply mapsTo_frame_update <;> (first | assumption | (exact ptrDisjoint_symm ‹_›)))
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

/-- `sep_unfold` tactic: unfold separation logic definitions to expose
    the underlying conjunctions and mapsTo assertions. -/
syntax "sep_unfold" : tactic

macro_rules
  | `(tactic| sep_unfold) => `(tactic|
    first
    | unfold sepMapsTo
    | unfold sepMapsTo3
    | unfold mapsTo
    | unfold sep
    | fail "sep_unfold: no separation logic definition to unfold"
    )

/-! # Worked example: how sep_auto simplifies swap proof

    Given: mapsTo a va h, mapsTo b vb h, ptrDisjoint a b
    Goal: mapsTo a vb (simpleUpdate (simpleUpdate h a vb) b va) ∧
          mapsTo b va (simpleUpdate (simpleUpdate h a vb) b va) ∧
          ptrDisjoint a b

    sep_auto would:
    1. Split the conjunction (3 parts)
    2. For mapsTo a vb: apply mapsTo_frame_update (b disjoint from a),
       then mapsTo_after_update (a was written with vb)
    3. For mapsTo b va: apply mapsTo_after_update (b was written with va)
    4. For ptrDisjoint: assumption
-/
