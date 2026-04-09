---
id: TASK-0070
title: 'L2 LocalVarExtract: implement full extraction (not just stub)'
status: To Do
assignee: []
created_date: '2026-04-09 19:34'
labels:
  - phase-5
  - lifting
dependencies: []
references:
  - ext/AutoCorres2/LocalVarExtract.thy
  - ext/AutoCorres2/local_var_extract.ML
  - Clift/Lifting/LocalVarExtract.lean
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
LocalVarExtract (L2) is currently a stub. Need MetaM or manual transformation that extracts local variables from the CState.locals record into lambda-bound Lean parameters. After L2, functions take locals as explicit arguments instead of reading from state. This is critical for clean user-facing proofs. Study ext/AutoCorres2/LocalVarExtract.thy and local_var_extract.ML.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 L2 transformation defined for arbitrary functions (not just gcd)
- [ ] #2 L2corres proven: L2 function refines L1 function under state projection
- [ ] #3 Tested on gcd, swap, and rotate3
- [ ] #4 No sorry in any L2corres proof
<!-- AC:END -->
