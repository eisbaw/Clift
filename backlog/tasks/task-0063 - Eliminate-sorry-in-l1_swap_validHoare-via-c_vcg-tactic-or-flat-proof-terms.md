---
id: TASK-0063
title: Eliminate sorry in l1_swap_validHoare via c_vcg tactic or flat proof terms
status: Done
assignee:
  - '@claude'
created_date: '2026-04-09 16:52'
updated_date: '2026-04-10 04:44'
labels:
  - phase-4
  - sorry
  - technical-debt
dependencies:
  - TASK-0046
references:
  - Examples/SwapProof.lean
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
SwapProof.lean:117 has a sorry in l1_swap_validHoare. The proof is mathematically trivial (deterministic computation trace) but hits two Lean 4 kernel limitations: (1) deep recursion limit when composing 7+ L1 Hoare rules, (2) have/let binding mismatch in structure update desugaring. Fix after Phase 4 c_vcg tactic is available, or by restructuring l1_swap_body to use flat CState.mk constructors instead of { s with ... }.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 l1_swap_validHoare proven with no sorry
- [x] #2 swap_correct depends only on propext/Quot.sound (no sorryAx)
- [x] #3 lake build produces no sorry warnings
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Attempted multiple proof strategies for l1_swap_validHoare:
1. Compositional Hoare rules (L1_hoare_seq + guard + modify) - fails: kernel deep recursion from nested rule composition
2. Direct set membership chaining (L1_guard_modify_result + L1_seq_singleton_ok) - fails: state naming hits have/let desugaring mismatch
3. Rewriting body with explicit constructors - fails: rfl check hits deep recursion
4. Combined vcg helpers (l1_vcg_guard, l1_vcg_modify) - gets furthest but still hits kernel deep recursion at ~7 nested levels

Root cause: Lean 4 kernel deep recursion limit on proof terms composed from 7+ nested Hoare rule applications. The proof is mathematically trivial but the kernel cannot handle the term depth.

Required solution: A MetaM-level VCG tactic that constructs FLAT proof terms by unfolding validHoare and directly building set membership witnesses, bypassing the compositional rule composition entirely.

Attempted swap proof decomposition with explicit constructor functions (swap_f1/f2/f3) to avoid deep kernel terms.
Result: L1corres proof works, but validHoare proof still hits kernel depth limits.
Root cause: ANY proof step that requires the kernel to reduce structure projections through composed functions (e.g., (swap_f1 s).globals) triggers deep recursion.
This is fundamental to Lean 4 kernel limits, not a proof strategy issue.
The sorry remains; workaround is the HeapLift-level proof (SwapHeapLift.lean).

Blocked by Lean 4 kernel depth limitation. SwapHeapLift.lean provides sorry-free proof at HeapLift level. L1-level proof needs MetaM VCG (task-0071) or upstream kernel fix (task-0076).

Solved via two-level projection lemma strategy: first-level projections (.globals, .locals) use show+rfl with hVal/heapUpdate [local irreducible] to limit kernel to single iota step; second-level projections (.locals.a, .globals.rawHeap) use rw with first-level lemma to avoid double-iota that triggered deep recursion. swap_correct depends on [propext, Classical.choice, Quot.sound] -- no sorryAx.

## What we tried (chronological)

### Attempt 1: Compositional Hoare rules (batch 4)
Applied L1_hoare_seq, L1_hoare_guard, L1_hoare_modify in sequence.
FAILED: 7+ nested rule applications created proof terms that exceeded kernel recursion depth (~512).

### Attempt 2: Direct set-membership reasoning
Unfolded L1.seq/guard/modify definitions, used rcases on result sets.
FAILED: rfl equalities between composed state terms (e.g., { s with globals := ... }) triggered kernel deep recursion via have/let desugaring mismatch.

### Attempt 3: Explicit constructor functions (swap_f1/f2/f3)
Replaced { s with ... } syntax with anonymous constructors ⟨s.globals, ⟨...⟩⟩.
PARTIALLY WORKED: L1corres proof succeeded. But validHoare proof still failed because projecting through composed functions (e.g., (swap_f1 s).globals.rawHeap) unfolded hVal's byte-level arithmetic.

### Attempt 4: Decomposed step lemmas with L1 Hoare rules
Added 10 L1 Hoare rule theorems (L1_hoare_modify, L1_hoare_guard, L1_hoare_seq, etc.).
FAILED: Composing even small numbers of these rules created proof terms too deep.

### Attempt 5: simp with projection lemmas (WHAT WORKED)
Key insight: the kernel depth issue is caused by hVal/heapUpdate unfolding, NOT by the structure nesting itself.

Solution:
1. attribute [local irreducible] hVal heapUpdate — stops kernel from unfolding byte arithmetic
2. @[simp] projection lemmas: swap_f1_globals : (swap_f1 s).globals = s.globals := rfl (works because kernel only does ONE iota reduction, doesn't need to unfold hVal)
3. simp only [swap_f1_globals, ...] BEFORE heapPtrValid encounters composed functions
4. Chain helper lemmas: L1_guard_modify_result, L1_seq_singleton_ok, L1_catch_singleton_ok

Build time: ~300ms. Proof checks instantly. The trick is preventing the kernel from ever seeing hVal inside a composition.

### Why previous attempts failed
All previous attempts let the kernel see `heapPtrValid (swap_f1 s).globals.rawHeap ...` before rewriting. The kernel would unfold heapPtrValid (universal quantifier over bytes), then try to reduce the argument, hitting hVal's UInt32 byte encoding (fromMem -> assembleByte -> BitVec -> Nat div/mod). The [local irreducible] attribute blocks this unfolding at the source.

### The general pattern for future proofs
For any L1 validHoare proof over state-modifying computations:
1. Define step functions with anonymous constructors (not { s with ... })
2. Mark hVal/heapUpdate as [local irreducible] 
3. Prove projection @[simp] lemmas for each step function
4. Use simp only with projection lemmas before any heapPtrValid reasoning
5. Chain L1_guard_modify_result / L1_seq_singleton_ok / L1_catch_singleton_ok
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Sorry in l1_swap_validHoare ELIMINATED. Zero sorry in entire codebase.

Fix: two-level projection lemma strategy with local irreducible marking.

1. Mark hVal and heapUpdate as [local irreducible] so kernel doesn't unfold byte-level arithmetic
2. Prove first-level projection lemmas (swap_f1_globals, swap_f1_locals) via show + explicit constructor + rfl
3. Use simp only with projection lemmas to rewrite state projections BEFORE heapPtrValid sees composed functions
4. Chain L1_guard_modify_result, L1_seq_singleton_ok, L1_catch_singleton_ok for step-by-step trace

swap_correct depends only on propext, Classical.choice, Quot.sound (standard Lean axioms, no sorryAx).
Build time for SwapProof.lean: ~300ms (was 20+ minutes with sorry).
<!-- SECTION:FINAL_SUMMARY:END -->
