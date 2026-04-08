---
id: TASK-0025
title: 'Phase 1 end-to-end: gcd.c through full pipeline with user proof'
status: To Do
assignee: []
created_date: '2026-04-08 21:36'
labels:
  - phase-1
  - test
  - milestone
dependencies:
  - TASK-0020
  - TASK-0024
references:
  - test/c_sources/gcd.c
  - Examples/GcdCorrect.lean
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The critical Phase 1 exit criterion: take gcd.c, run CImporter, apply SimplConv (L1), apply LocalVarExtract (L2), then prove gcd_correct as a user-level Hoare triple that chains all the way back to the C semantics. If this works, the architecture is validated.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 gcd.c -> CImporter -> Generated/Gcd.lean compiles
- [ ] #2 SimplConv produces L1 gcd with L1corres proof
- [ ] #3 LocalVarExtract produces L2 gcd with L2corres proof
- [ ] #4 theorem gcd_correct : validHoare P l2_gcd Q proven in Examples/GcdCorrect.lean
- [ ] #5 Proof chains back to C: corres_trans composes L1corres and L2corres
- [ ] #6 just e2e passes (all snapshots, all proofs)
<!-- AC:END -->
