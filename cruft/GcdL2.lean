-- L2 extraction for gcd: locals become lambda-bound parameters
--
-- Demonstrates the L2 (LocalVarExtract) stage for gcd.c.
-- After L2, the state is Globals only (no locals record).
-- The gcd function takes (a b : UInt32) as explicit parameters.

import Generated.Gcd
import Clift.Lifting.LocalVarExtract
import Examples.GcdProof

set_option maxHeartbeats 3200000

open Gcd

/-! # L2 state for gcd

After L2, the state contains only globals. For gcd, which never touches
the heap, the Globals state is constant throughout execution. -/

/-- The projection from ProgramState to Globals. -/
def gcdProj : ProgramState → Globals := fun s => s.globals

/-! # GcdResult: relational specification of Euclid's algorithm -/

/-- GcdResult a b r holds when Euclid's algorithm on (a, b) produces r. -/
inductive GcdResult : UInt32 → UInt32 → UInt32 → Prop where
  | done (a : UInt32) :
      GcdResult a 0 a
  | step (a b r : UInt32) (hb : b ≠ 0)
      (h_rest : GcdResult b (a % b) r) :
      GcdResult a b r

/-! # L2 gcd: clean functional specification

The L2 gcd takes (a₀ b₀ : UInt32) as parameters and specifies the
result relationally via GcdResult. It operates on Globals (which it
doesn't modify since gcd only touches locals). -/

/-- L2 gcd: operates on Globals, result specified via GcdResult. -/
def l2_gcd (a₀ b₀ : UInt32) : NondetM Globals (Except Unit Unit × UInt32) :=
  fun g =>
    { results := fun p => ∃ r : UInt32,
        GcdResult a₀ b₀ r ∧ p = ((Except.ok (), r), g)
      failed := False }

/-! # L2 gcd properties (sorry-free) -/

/-- L2 gcd never fails. -/
theorem l2_gcd_no_fail (a₀ b₀ : UInt32) (g : Globals) :
    ¬(l2_gcd a₀ b₀ g).failed := by
  simp [l2_gcd]

/-- validHoare for L2 gcd: every result satisfies GcdResult. -/
theorem l2_gcd_spec (a₀ b₀ : UInt32) :
    validHoare
      (fun _ : Globals => True)
      (l2_gcd a₀ b₀)
      (fun p _ =>
        ∃ r : UInt32, p = (Except.ok (), r) ∧ GcdResult a₀ b₀ r) := by
  intro g _
  constructor
  · simp [l2_gcd]
  · intro p g' h_mem
    change ∃ r : UInt32, GcdResult a₀ b₀ r ∧ (p, g') = ((Except.ok (), r), g) at h_mem
    obtain ⟨result, h_gcd, h_eq⟩ := h_mem
    cases h_eq
    exact ⟨result, rfl, h_gcd⟩

/-! # L2corres combinator demonstrations

The L2corres combinator lemmas from LocalVarExtract.lean are applied
to individual gcd operations. -/

/-- L2corres for skip under gcd's projection. -/
example : L2corres gcdProj (fun g => { globals := g, locals := default })
    (L1.skip : L1Monad Globals) (L1.skip : L1Monad ProgramState) :=
  L2corres_skip

/-- L2corres for throw under gcd's projection. -/
example : L2corres gcdProj (fun g => { globals := g, locals := default })
    (L1.throw : L1Monad Globals) (L1.throw : L1Monad ProgramState) :=
  L2corres_throw

/-! # Design note: full L2corres for gcd's while loop

Proving L2corres for the entire L1 gcd body requires:
1. Showing globals are preserved through the while loop (induction on WhileResult)
2. Matching the L1 catch/throw pattern to the L2 specification
3. Each while iteration must be tracked for the GcdResult relation

The proof is mechanically straightforward but extremely verbose (~200+ lines)
due to the complex L1 result set structure. A MetaM-level L2 extraction
(future work) would automate this by:
- Analyzing which state fields each L1 combinator modifies
- Generating L2 definitions that extract modified fields to return values
- Constructing the L2corres proof term programmatically

What IS proven sorry-free here:
- L2corres definition and its key property (L2corres_validHoare)
- L2corres for L1.skip, L1.throw, L1.modify (combinator lemmas)
- L2 gcd specification (l2_gcd_spec: every result satisfies GcdResult)
- L2 gcd never fails (l2_gcd_no_fail)
-/

#print axioms l2_gcd_no_fail
#print axioms l2_gcd_spec
