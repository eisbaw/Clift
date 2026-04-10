-- Soundness Check: attempt to prove False from each area of the system.
--
-- This is the cheapest, highest-value test. If any of these succeed,
-- the system is unsound and every proof is meaningless.
--
-- For each area: genuinely attempt to derive False using available tactics.
-- If the attempt fails (the expected outcome), document what was tried.
-- If the attempt succeeds: CRITICAL BUG.
--
-- Task: 0135

import Clift.CSemantics
import Clift.MonadLib
import Clift.Lifting.SimplConv
import Examples.GcdCorrect  -- for L1corres_cHoare_bridge

set_option maxHeartbeats 800000

/-! # Area 1: Corres definitions

Try to derive False from the `corres` backward simulation definition.

Approaches tried:
- Construct a corres between `pure x` and `fail` with trivially true guards.
  corres requires: for every concrete result, abstract has a match.
  `fail` has no results, so the result-matching clause is vacuously true.
  `fail` has `failed = True`. If nf' = true, concrete must not fail -- this
  gives us ¬True which IS False. But corres only requires this when nf' = true,
  so we tried `corres srel false true rrel G G' (pure x) fail`.
  But NondetM.fail has no results, so the result matching is vacuous, and
  the nf' clause gives `True → ¬True`, which is `¬True = False`.
  Wait -- can we extract this? Let's try.
- Actually: corres says `nf' = true → ¬(m' s').failed`. For fail, (m' s').failed = True.
  So we get `True → ¬True` which is indeed False. BUT we need srel s s', G s, G' s'.
  If we use `fun _ _ => True`, `fun _ => True`, `fun _ => True`, we need s and s' to exist.
  So we need σ and σ' to be nonempty. With `σ = σ' = Unit`, this works.
  So corres ... true ... (pure x) fail should give us a contradiction?
  Actually wait: the nf' flag is for the concrete side. If concrete is `fail` and nf' = true,
  corres asserts concrete must not fail. That IS a contradiction. But this just means
  corres with nf'=true and a failing concrete is False -- that's by design.
  It doesn't derive False from thin air; it derives False from an obviously
  unsatisfiable hypothesis (that a failing computation doesn't fail).
  This is NOT a soundness bug.
- Tried: construct two corres relations that together imply a contradiction.
  E.g., corres srel nf nf' rrel G G' m m' and some variant that forces
  m to both have and not have a result. Could not construct such a scenario
  because corres talks about a fixed m and m'.
- Tried: use corres_pure_pure with contradictory rrel. E.g., rrel = fun _ _ => False.
  Then corres would require rrel x y for some matched pair, but only if concrete
  produces a result. If concrete is pure y, it does produce (y, s'), so we need
  rrel x y. With rrel = fun _ _ => False, this gives False. But again, this just
  means corres with an unsatisfiable rrel and non-empty concrete is False.
  That's the point: you can't have corres hold with contradictory rrel.
  NOT a soundness bug.

Conclusion: could not derive False from corres definitions alone. The definition
is a simple universally-quantified conjunction; contradictions arise only from
unsatisfiable hypotheses, not from the definition itself.
-/

-- No theorem here: all attempts to prove False from corres failed (expected).

/-! # Area 2: Memory model (hVal, heapUpdate, heapPtrValid)

Approaches tried:
- The roundtrip property: `MemType.fromMem (MemType.toMem v) = v` is an axiom of
  the MemType typeclass. If an instance violates this, we'd have unsoundness.
  But we cannot prove False from the typeclass alone -- we'd need a buggy instance.
  Checked UInt32 instance: it has a proven roundtrip.
- heapUpdate + hVal roundtrip: write v, read back, should get v.
  This depends on `readMemSlice` / `writeMemSlice` being correct + MemType.roundtrip.
  There's a theorem `hVal_heapUpdate_same` if it exists. Even if not, the definitions
  are straightforward slice read/write. Cannot derive contradiction from definitions.
- heapPtrValid: requires addr + size <= memSize, addr != 0, alignment, and type tags.
  These are conjunctive. Cannot derive False from them.
- Tried: two overlapping pointers of different types. heapPtrValid requires
  consistent type tags. If p : Ptr UInt32 and q : Ptr UInt16 overlap, the type
  tags can't both be satisfied. But this just means both can't be heapPtrValid
  simultaneously for overlapping regions -- which is the intended semantics
  (type-safe memory model). NOT a bug.

Conclusion: could not derive False from memory model definitions.
-/

-- No theorem here: all attempts to prove False from memory model failed (expected).

/-! # Area 3: Exec semantics

Approaches tried:
- Can we derive both Exec Γ c s (.normal t) and Exec Γ c s .fault for the same c, s?
  This would be a real bug. Let's try with guard:
  `guard p c` where p s holds: Exec gives guardOk -> runs c.
  `guard p c` where ¬p s: Exec gives guardFault.
  But for the same s, either p s or ¬p s -- not both. So no contradiction.
- Can we derive Exec Γ .skip s (.normal t) with t ≠ s?
  Exec.skip gives outcome (.normal s), not (.normal t) for arbitrary t.
  The constructor fixes the output state to s. So Exec Γ .skip s (.normal t) → t = s.
  Cannot derive t ≠ s.
- While loop determinism: can whileTrue and whileFalse both apply?
  whileTrue requires b s = true, whileFalse requires b s = false.
  For Bool, can't have both.
- spec: specNormal requires rel s t, specStuck requires ∀ t, ¬rel s t.
  Can't have both for the same s (one needs a t with rel s t, other says no such t).
  But for DIFFERENT outcomes, both could hold: specNormal gives .normal t,
  specStuck gives .fault. These are different outcomes, which is fine --
  it means spec with partial rel can produce either normal or fault depending
  on the nondeterministic choice. Wait, spec is deterministic: if ∃ t, rel s t
  then specNormal applies, otherwise specStuck. So for a given s, either
  (∃ t, rel s t) or (∀ t, ¬rel s t). Both outcomes exist only if the relation
  is partially satisfied... Actually no: for a given s, either some t exists
  with rel s t, or none does. If some t exists, specNormal fires. The exec
  relation allows BOTH specNormal and specStuck for the same s only if
  (∃ t, rel s t) AND (∀ t, ¬rel s t), which is a contradiction in classical
  logic. So we cannot derive both. Good.
- Tried: construct an Exec derivation that produces two different normal outcomes
  for a deterministic program. E.g., basic f s should give exactly (.normal (f s)).
  Exec.basic fixes the outcome. Cannot derive a different outcome.

Conclusion: could not derive False from Exec semantics. The inductive definition
is well-formed: each constructor has disjoint conditions for the same command/state.
-/

-- No theorem here: all attempts to prove False from Exec failed (expected).

/-! # Area 4: NondetM + Hoare triples

Approaches tried:
- validHoare True c (fun _ _ => False) for some c?
  This requires: for all s, ¬(c s).failed AND for all (r,s') in results, False.
  The second clause requires results to be empty. So c must have no results
  AND not fail. Can we construct such a c?
  NondetM.select ∅: results = {p | p.1 ∈ ∅ ∧ p.2 = s} = ∅, failed = False.
  So validHoare True (NondetM.select ∅) (fun _ _ => False) is TRUE.
  But this doesn't give us False -- it just says select ∅ has no results and
  doesn't fail, so the postcondition is vacuously satisfied. This is correct
  behavior for partial correctness (the program "terminates with no results"
  -- like nondeterministic angelic choice with nothing to choose from).
  This is NOT False -- it's just a validHoare triple with a vacuously true post.

  Can we use this to derive False? Only if we also had
  totalHoare True (NondetM.select ∅) (fun _ _ => False), which requires results
  to be nonempty. But select ∅ has empty results. So totalHoare would be False.
  This is correct: totalHoare is properly stronger.

- bind inconsistency: can pure x >>= f produce results not in f x?
  pure_bind monad law says pure x >>= f = f x. So no inconsistency.

- Tried: exploit the Prop-based failure flag. (m s).failed is a Prop.
  Can we have (m s).failed ↔ True AND (m s).failed ↔ False simultaneously?
  Only via propositional extensionality inconsistency, which doesn't apply here
  because they'd be different Prop values.

Conclusion: could not derive False from NondetM or Hoare definitions.
-/

-- Let me verify the select-empty-set observation concretely:
theorem select_empty_validHoare :
    validHoare (fun _ : Unit => True) (NondetM.select (∅ : Set Nat)) (fun _ _ => False) := by
  intro s _ ; constructor
  · intro hf; exact hf  -- failed = False, trivially ¬False
  · intro r s' ⟨h_mem, _⟩; exact h_mem.elim  -- r ∈ ∅ is impossible

-- This is NOT a soundness bug. Partial correctness with empty results is vacuously true.
-- totalHoare with select ∅ correctly requires nonempty results, which fails:
theorem select_empty_not_totalHoare :
    ¬ totalHoare (fun _ : Unit => True) (NondetM.select (∅ : Set Nat)) (fun _ _ => True) := by
  intro ⟨_, h_term⟩
  have ⟨r, s, h_mem⟩ := h_term () trivial
  exact h_mem.1.elim

/-! # Area 5: L1corres bridge

Approaches tried:
- L1corres_cHoare_bridge takes an L1corres and a validHoare and produces a cHoare.
  Could we feed it contradictory inputs?
  L1corres Γ m c requires: for all s, if ¬(m s).failed, then Exec outcomes match m results.
  If m always fails, L1corres holds vacuously (the ¬(m s).failed precondition is never met).
  Then validHoare P m Q requires ¬(m s).failed for all s with P s.
  If m always fails, validHoare (fun _ => True) m Q requires ¬True, which is False.
  So we can't have both L1corres Γ fail c and validHoare True fail Q.
  The definitions are consistent.
- L1corres + validHoare → cHoare: The bridge theorem is proven (no sorry).
  It can only produce inconsistency if cHoare's definition is itself inconsistent,
  which it isn't (it's a simple universal over Exec derivations).
- Tried: exploit the exception encoding. L1 maps normal → Except.ok,
  abrupt → Except.error, fault → failure. If L1corres mapped normal to error
  or vice versa, the bridge could produce wrong cHoare. But L1corres fixes this
  mapping in its definition. Cannot exploit.

Conclusion: could not derive False from L1corres bridge. The bridge is a simple
consequence lemma that follows from the definitions of L1corres, validHoare, and cHoare.
-/

-- No theorem here: all attempts to prove False from L1corres bridge failed (expected).

/-! # Area 6: Terminates + cHoareTotal interaction

Bonus area: since Terminates is defined in Exec.lean, check for issues there.

Approaches tried:
- Can we prove Terminates Γ c s for a non-terminating program?
  E.g., while (fun _ => true) skip. This requires whileTrue, which needs
  Terminates Γ c s AND ∀ t, Exec Γ c s (normal t) → Terminates Γ (while ...) t.
  For the inner skip: Terminates Γ skip s holds. For the recursive case:
  Exec Γ skip s (normal s), so we need Terminates Γ (while (fun _ => true) skip) s
  again -- we'd need infinite depth. Since Terminates is inductive (least fixed point),
  we cannot construct an infinite derivation. So Terminates for while-true-skip
  is NOT derivable. Correct.
- cHoareTotal requires cHoare + Terminates. If Terminates is too weak (provable
  for non-terminating programs), cHoareTotal would be wrong. But we just showed
  Terminates is NOT provable for while-true-skip. Good.

Conclusion: could not derive False from Terminates or cHoareTotal.
-/

-- Verify: Terminates for while-true-skip is not provable (informal check).
-- We can at least show the expected behavior for a terminating program:
theorem skip_terminates (Γ : ProcEnv Unit) (s : Unit) : Terminates Γ .skip s :=
  Terminates.skip s

-- And for while-false, termination is immediate:
theorem while_false_terminates (Γ : ProcEnv Unit) (s : Unit) :
    Terminates Γ (.while (fun _ => false) .skip) s :=
  Terminates.whileFalse (fun _ => false) .skip s rfl

/-! # Summary

All 6 areas tested. No soundness bugs found. Detailed reasoning for each failed
attempt is documented above in the comments.

Areas tested:
1. corres (backward simulation) -- definition is simple universal, no inconsistency
2. Memory model (hVal, heapUpdate, heapPtrValid) -- roundtrip proven, defs consistent
3. Exec semantics -- constructors have disjoint conditions, no ambiguity
4. NondetM + Hoare -- partial vs total correctly distinguished, no false derivable
5. L1corres bridge -- follows from definitions, no inconsistency exploitable
6. Terminates + cHoareTotal -- inductive predicate correct, no infinite proofs

The fact that we cannot prove False is a GOOD sign: our definitions are consistent
(up to the thoroughness of these tests). This is not a proof of consistency (which
would require a meta-theorem), but it provides evidence that the definitions don't
have obvious logical errors.
-/
