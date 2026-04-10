---
id: TASK-0128
title: 'Binary verification: compiled code matches C semantics'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-10 15:30'
updated_date: '2026-04-10 18:10'
labels:
  - phase-i
  - binary
  - industrial
dependencies: []
references:
  - ext/sel4-comprehensive-tocs2014.pdf
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
seL4 verified the compiled ARM binary matches the C semantics (translation validation). This closes the compiler trust gap. Approaches: (1) verify against a specific compiler (gcc/clang at specific -O level) by decompiling the binary and proving it matches CSimpl, (2) use a verified compiler (CompCert) so the compiler itself is trusted, (3) use translation validation (compile with any compiler, post-hoc prove the binary is correct). Study ext/sel4-comprehensive-tocs2014.pdf Section 5 for seL4's approach.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Approach selected and documented as ADR
- [ ] #2 Prototype: compile one C function, decompile binary, prove matches CSimpl
- [x] #3 Or: CompCert integration path documented
- [x] #4 Trust model documented: what's in the TCB after binary verification?
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
AC#2 (prototype): ADR documents why a prototype is not practical without an ISA model. The assessment section covers what would be needed for a single-function prototype. This is an honest 'not feasible yet' rather than a half-baked attempt.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
ADR-008 documenting binary verification approaches:
- Translation validation: feasible but requires ISA model (2-5 person-years per arch)
- CompCert (recommended): verified compiler, minimal effort, cross-prover trust acceptable
- Lean-as-compiler: not feasible with current infrastructure
- Prototype assessment: even trivial function needs ISA model, calling convention model, instruction semantics
- Trust model documented for each approach
- Decision: CompCert primary, translation validation for highest assurance
<!-- SECTION:FINAL_SUMMARY:END -->
