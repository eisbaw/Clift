-- L1 VCG test: verify L1 Hoare proof infrastructure

import Generated.Swap
import Clift.Tactics.L1Vcg
import Clift.Lifting.L1Auto
import Clift.Lifting.L1HoareRules

set_option maxHeartbeats 12800000
set_option maxRecDepth 4096

clift_l1 Swap

/-! # Test 1: L1_guard_modify_result (the workhorse lemma)

This is the core of the SwapProof pattern: characterize the result of
a guard+modify step as a singleton set. -/

theorem swap_step1_result (s : Swap.ProgramState)
    (h : heapPtrValid s.globals.rawHeap s.locals.a) :
    let step := L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.a))
                       (L1.modify fun s => { s with locals := { s.locals with t := hVal s.globals.rawHeap s.locals.a } })
    (step s).results = {(Except.ok (), { s with locals := { s.locals with t := hVal s.globals.rawHeap s.locals.a } })} ∧
    ¬(step s).failed :=
  L1_guard_modify_result _ _ s h

/-! # Test 2: Direct Hoare proof via intro

When the postcondition is simple, direct intro proofs work. -/

theorem test_modify_hoare :
    validHoare
      (fun _ : Swap.ProgramState => True)
      (L1.modify fun s => s)
      (fun r s => r = Except.ok () ∧ True) := by
  intro s _
  constructor
  · intro hf; exact hf
  · intro r s₁ hmem
    have ⟨h1, h2⟩ := Prod.mk.inj hmem
    subst h1; subst h2
    exact ⟨rfl, trivial⟩

/-! # Test 3: The l1_vcg tactic shell

The tactic applies L1 Hoare rules. It currently works for the guard'
and modify' rules when the precondition/postcondition shapes match. -/

-- This verifies the tactic infrastructure compiles and is available
-- The actual tests require properly shaped pre/postconditions
-- which is the MetaM automation gap

#check @L1_hoare_guard'
#check @L1_hoare_modify'
#check @L1_hoare_seq_ok
#check @L1_hoare_catch_ok
#check @L1_hoare_skip

#print axioms swap_step1_result
#print axioms test_modify_hoare

/-! # Assessment

Working infrastructure:
1. L1_guard_modify_result: characterizes guard+modify steps (PROVEN)
2. L1_seq_singleton_ok: chains singleton-result steps (PROVEN)
3. L1_catch_singleton_ok: wraps in catch (PROVEN)
4. L1 Hoare rules: guard, modify, seq, catch, skip (PROVEN)
5. l1_vcg tactic shell: applies rules when shapes match

Limitation blocking full swap automation:
- Lean's higher-order unifier cannot infer intermediate conditions R
  when the postcondition involves `fun _ => True` or complex structure updates
- The l1_vcg macro tactic uses `apply` which depends on unification
- A MetaM tactic that COMPUTES R backwards (weakest precondition) would fix this

The SwapProof.lean approach (results-level lemmas) remains the working
pattern for pointer-heavy functions. The VCG tactic helps with decomposition
but cannot yet infer intermediate conditions automatically. -/
