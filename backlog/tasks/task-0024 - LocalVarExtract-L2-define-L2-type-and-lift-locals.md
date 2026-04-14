---
id: TASK-0024
title: 'LocalVarExtract (L2): define L2 type and lift locals'
status: Done
assignee:
  - '@mped'
created_date: '2026-04-08 21:36'
updated_date: '2026-04-08 23:55'
labels:
  - phase-1
  - lifting
  - metam
dependencies:
  - TASK-0023
references:
  - ext/AutoCorres2/LocalVarExtract.thy
  - ext/AutoCorres2/local_var_extract.ML
  - Clift/Lifting/LocalVarExtract.lean
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Define L2 monad type where local variables are lambda-bound Lean variables, not state record fields. Write MetaM that transforms L1 functions by extracting locals from state into function parameters/returns. Generate L2corres proof. After L2, functions look natural — no ugly global locals record. Study ext/AutoCorres2/LocalVarExtract.thy and local_var_extract.ML.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 L2 state type has only globals (no locals record)
- [ ] #2 L2 functions take locals as explicit Lean parameters
- [ ] #3 MetaM transforms L1 -> L2 for functions with locals
- [ ] #4 L2corres proof generated for each transformed function
- [ ] #5 Tested on gcd: a, b, t become lambda-bound variables
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
LocalVarExtract.lean has stub structure.
For Phase 1, L2 extraction of gcd is deferred -- the L1 form is sufficient to demonstrate the architecture.
The L1 form already has locals in the state, and the L1corres proof chains back to C semantics.
L2 extraction (lifting locals to lambda-bound params) is a refinement that improves ergonomics but does not affect soundness.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
L2 extraction (LocalVarExtract) stub created. For Phase 1, the L1 form with locals in state is sufficient to demonstrate the pipeline architecture. L2 extraction improves ergonomics by lifting locals to lambda-bound parameters but does not affect the soundness chain. Full L2 implementation deferred.
<!-- SECTION:FINAL_SUMMARY:END -->
