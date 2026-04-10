---
id: TASK-0128
title: 'Binary verification: compiled code matches C semantics'
status: To Do
assignee: []
created_date: '2026-04-10 15:30'
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
- [ ] #1 Approach selected and documented as ADR
- [ ] #2 Prototype: compile one C function, decompile binary, prove matches CSimpl
- [ ] #3 Or: CompCert integration path documented
- [ ] #4 Trust model documented: what's in the TCB after binary verification?
<!-- AC:END -->
