---
id: TASK-0233
title: Split RBExtFuncSpecs.lean into per-function proof modules
status: To Do
assignee: []
created_date: '2026-04-12 10:37'
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
