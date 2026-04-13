---
id: TASK-0235
title: Implement L1ProcEnv compositional call reasoning for inter-procedural proofs
status: In Progress
assignee:
  - '@claude'
created_date: '2026-04-12 17:01'
updated_date: '2026-04-12 23:59'
labels:
  - infrastructure
  - inter-procedural
  - sorry-elimination
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Inter-procedural proofs (functions calling other functions via dynCom+L1.call) are blocked across 8 sorry in 3 files. The L1 body inlines the callee via L1.call l1ProcEnv "name", which resolves to the FULL callee body. When Lean elaborates or kernel-checks through dynCom, it unfolds the entire callee body into the proof term, causing OOM (>15GB per proof) or kernel deep recursion.

WHAT IS NEEDED:
1. L1ProcEnv lookup lemma: a theorem proving `l1ProcEnv "callee_name" = some l1_callee_body` that can be used without unfolding the body. Proved via simp with all L1 bodies marked [local irreducible].
2. L1_hoare_call_spec composition: use the callee's already-proven validHoare spec at the call site, NOT re-proving the callee inline. Pattern: if callee_spec.satisfiedBy callee_body is proven, then at the call site, apply the spec's pre/post directly.
3. dynCom frame reasoning: after the call, dynCom does save/setup/call/restore. Need to prove: (a) setup establishes callee precondition, (b) callee spec gives postcondition, (c) restore maps callee result back to caller state, (d) heap changes from callee are preserved through restore (only locals change, not globals).

AFFECTED SORRY (8 total):
- HashTableProof.lean (3): ht_insert, ht_lookup — dynCom calls ht_hash
- RBExtProofsSorry.lean (3): rb_check_integrity (calls rb_count_nodes), rb_push_if_not_full (calls rb_push), rb_pop_if_not_empty (calls rb_pop)
- PriorityQueueProof.lean (2): pq_insert (calls pq_bubble_up), pq_extract_min (calls pq_bubble_down)

WHAT HAS BEEN TRIED AND WORKS:
- L1ProcEnv lookup via simp with [local irreducible] on all L1 bodies — HashTable agent proved: l1ProcEnv "ht_hash" = some l1_ht_hash_body (see HashTableProof.lean ~line 528)
- ht_hash_ok/ht_hash_full theorems packaging the hash result (see HashTableProof.lean ~line 534)
- PriorityQueue agent proved: insert_l1Γ "pq_bubble_up" = some l1_pq_bubble_up_body (see PriorityQueueProof.lean ~line 340)

WHAT DOES NOT WORK (kernel depth / OOM):
- Unfolding L1.dynCom directly in the proof — the dynCom term contains the full callee body plus save/restore lambdas, totaling thousands of constructor nodes. With 40-field Locals struct, each { s with locals := ... } expands to ~40 fields, and the kernel's ~512 recursion depth limit is exhausted.
- Using `show` to reshape the goal for dynCom decomposition — typeclass resolution for DecidablePred fails on wildcard goals
- Building the full proof term inline — OOM at >15GB even for simple callees like ht_hash
- Any approach that requires the kernel to carry the callee body through the proof term

RECOMMENDED APPROACH:
1. Define L1_hoare_dynCom_call rule: given (a) L1ProcEnv lookup succeeds, (b) setup function establishes callee precondition from caller state, (c) callee validHoare is proven, (d) restore function maps callee result to caller postcondition — then the dynCom+call satisfies the caller's Hoare triple. This keeps the callee body OPAQUE in the proof term.
2. All step functions (setup, restore) must use anonymous constructors ⟨globals, ⟨f1,...,fN⟩⟩ not { s with ... } to avoid kernel depth on large Locals structs.
3. Mark callee L1 bodies as [local irreducible] during the caller proof to prevent kernel from unfolding them.
4. The L1ProcEnv lookup should be a pre-computed simp lemma, not derived inline.

REFERENCE PATTERNS:
- SwapProof.lean: anonymous constructor + two-step projection pattern
- HashTableProof.lean lines 528-608: L1ProcEnv lookup + ht_hash_ok/full
- PriorityQueueProof.lean lines 320-385: L1ProcEnv definitions + lookup theorems
- FuncSpec.lean: L1_hoare_call_spec (exists but not yet used in any proof)
- feedback_lean4_kernel_depth.md: [local irreducible] hVal heapUpdate pattern

IMPLEMENTATION FILE: Clift/Lifting/L1HoareRules.lean (add L1_hoare_dynCom_call rule)
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 L1_hoare_dynCom_call theorem proven in L1HoareRules.lean
- [ ] #2 At least one inter-procedural sorry eliminated using the new rule
- [ ] #3 Pattern documented with example (e.g. rb_check_integrity calling rb_count_nodes)
- [x] #4 No kernel depth or OOM issues in the proof
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
$1. Add L1_hoare_call, L1_hoare_dynCom_basic, L1_hoare_dynCom_call to L1HoareRules.lean\n2. Add L1_catch_skip_ok_only helper lemma\n3. Prove rb_check_integrity_validHoare using the new rules\n4. Build and verify
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
2026-04-12: nanoda (Rust lean kernel checker) researched — it is a post-processing verifier on export files, not a drop-in kernel replacement during lake build. Cannot help with OOM during elaboration. The RAM issue is in Lean elaborator creating huge proof terms for 40-field structs, not in kernel checking. Solutions: (1) reduce proof term size via opaque helpers, (2) split import chains, (3) use lake build -j1, (4) implement L1_hoare_dynCom_call to keep callee bodies opaque.
<!-- SECTION:NOTES:END -->
