---
id: TASK-0254
title: Replace native_decide with decide in proof-critical paths
status: To Do
assignee: []
created_date: '2026-04-14 18:06'
labels:
  - credibility
  - soundness
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
native_decide trusts the Lean COMPILER (not the kernel) to evaluate decidable propositions. A compiler bug could produce a false proof that the kernel accepts. This undermines the entire verification chain.

3 proof-critical uses found:

1. Clift/Tactics/CorresAuto.lean:140 — corres_auto tactic emits native_decide as fallback. Fix: change to decide. If decide is too slow, use simp or omega instead.

2. Examples/ListLengthProof.lean:145 — proves (1:UInt32).toNat = 1. Fix: replace with `decide` or `rfl` (this is trivially kernel-checkable).

3. Examples/PriorityQueueProof.lean:344 — L1ProcEnv lookup. Fix: replace with `simp [L1.L1ProcEnv.insert]` (same pattern used in HashTableProof.lean).

8 additional uses in Examples/AI*Test.lean files are NOT proof-critical (test/demo code). Low priority but should also be cleaned up.

POLICY: native_decide should NEVER appear in correctness proofs. Add to just audit.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 CorresAuto.lean native_decide replaced with decide/simp
- [ ] #2 ListLengthProof.lean native_decide replaced
- [ ] #3 PriorityQueueProof.lean native_decide replaced
- [ ] #4 native_decide check added to just audit
- [ ] #5 Zero native_decide in Clift/ and proof-critical Examples/
<!-- AC:END -->
