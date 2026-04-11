---
name: Sorry elimination patterns and blockers
description: Detailed patterns for eliminating sorry in Clift L1 validHoare proofs, including kernel depth workarounds and what blocks each category
type: feedback
---

## Sorry categories and how to fix each

### 1. Pure functions (no heap, no loops)
- **Fix**: `unfold; simp; omega/decide/native_decide`
- **Example**: conn_state_valid_correct in StateMachineProof.lean

### 2. Heap accessor (single guard+modify+throw+catch+skip)
- **Fix**: `L1_guard_modify_throw_catch_skip_result` + projection lemmas
- **Example**: rb_capacity, rb_size in RBExtFuncSpecs.lean

### 3. Conditional (L1.condition)
- **Fix**: `L1_elim_cond_true`/`L1_elim_cond_false` to case-split, then pattern 2
- **Example**: isArchObjectType_correct in Sel4CapProof.lean

### 4. Multi-step heap mutation (5+ guard+modify pairs)
- **Fix**: `L1_hoare_guard_modify_fused` + `L1_hoare_guard_modify_chain2/3`
- **Blocker**: Need `ptrDisjoint` in preconditions for `hVal_heapUpdate_disjoint`
- **Blocker**: Kernel depth for 40-field Locals struct — MUST use anonymous constructors + [local irreducible]
- **Key**: Each step function defined as `fun s => ⟨s.globals_part, ⟨fields...⟩⟩`, NOT `{ s with ... }`

### 5. Loop functions
- **Fix**: `L1_hoare_while` with loop invariant I
- **Template**: rb_count_nodes proof in RBExtFuncSpecs.lean
- **Blocker**: Body preservation proof hits kernel depth for 4+ step bodies
- **Workaround**: Merge consecutive modifies into one (L1_merge_assignments pattern)

### 6. Inter-procedural (function calls)
- **Fix**: `L1_hoare_call_spec` from FuncSpec.lean
- **Prerequisite**: Callee's validHoare must be proven first

## The kernel depth problem

Lean 4 kernel has ~512 recursion depth limit. After `subst`, it expands `{ s with locals := { s.locals with field := v } }` into a 40-field record. Projections through this hit the limit.

**Workaround**: `attribute [local irreducible] hVal heapUpdate` + `@[simp]` projection lemmas as rfl proofs. This prevents the kernel from unfolding through the composed functions.

**How to apply**: See SwapProof.lean for the complete pattern.

## AutoCorres2 tactics we should port

1. `L1_merge_assignments`: fuses `seq (modify f) (seq (modify g) k)` into `seq (modify (g ∘ f)) k`
2. `runs_to_vcg`: named rule set that decomposes bind/while/guard automatically
3. `L1_while_lp`: while Hoare rule (we have this as L1_hoare_while)
4. `L2_opt` peephole: simplifies seq-skip, trim-after-throw, guard-true/false
5. Congruence rules for rewriting under guards

## Key lemmas in L1HoareRules.lean

- `L1_guard_modify_result`: singleton result set for guard+modify
- `L1_seq_singleton_ok`: if m1 is singleton ok, seq results are m2 at that state
- `L1_catch_singleton_ok`/`error_singleton`: catch on singleton body
- `L1_modify_throw_catch_skip_result`: common return pattern
- `L1_hoare_guard_modify_fused`: one-step guard+modify Hoare rule
- `L1_hoare_guard_modify_chain2/3`: composed guard+modify chains
- `L1_hoare_while`: loop Hoare rule with invariant
- `L1_elim_cond_true/false`: condition elimination in L1.seq
