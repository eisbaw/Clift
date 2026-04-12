---
id: TASK-0233
title: Split RBExtFuncSpecs.lean into per-function proof modules
status: In Progress
assignee:
  - '@claude'
created_date: '2026-04-12 10:37'
updated_date: '2026-04-12 12:48'
labels:
  - infrastructure
  - scaling
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
RBExtFuncSpecs.lean is now 3500+ lines and builds require >20GB RAM, causing OOM kills. Split into smaller files (e.g. RBPushProof.lean, RBLoopProofs.lean, RBInterProcProofs.lean) to make iterative proof development tractable. Each file should import the specs and prove a subset of functions.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 RBExtFuncSpecs.lean split into 3-5 smaller files
- [ ] #2 Each file builds independently in <10GB RAM
- [ ] #3 All existing proofs preserved
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
$1. Create RBExtSpecs.lean with all FuncSpec defs, LinkedListValid, RelFuncSpec, shared helpers (validHoare_weaken_trivial_post, type tag helpers, projection lemmas, conditional helpers, multi-guard helpers)\n2. Create RBExtProofsSimple.lean with 7 accessor validHoare + 7 totalHoare proofs\n3. Create RBExtProofsLoops.lean with rb_push proof + all loop proofs (count_nodes, contains, find_index, nth, sum, count_above, count_at_or_below, max, min)\n4. Create RBExtProofsSorry.lean with all 15 sorry theorems\n5. Update lakefile.lean to replace RBExtFuncSpecs with the 4 new modules\n6. Update RBExtRefinement.lean to import all 4 new files\n7. Build and verify sorry count unchanged at 15\n8. Remove original RBExtFuncSpecs.lean
<!-- SECTION:PLAN:END -->
