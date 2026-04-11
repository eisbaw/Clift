---
id: TASK-0214
title: 'Mutation testing: inject bugs in CImporter, verify proofs catch them'
status: To Do
assignee: []
created_date: '2026-04-11 06:29'
labels:
  - maturity
  - testing
  - hardening
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Trust but verify the TCB. Inject deliberate bugs in the CImporter (swap two operands, drop a guard, change a type), regenerate .lean, run lake build. If the proofs STILL pass, we have a false-positive gap — the proofs don't actually depend on the part we broke. This tests proof COVERAGE, not just proof EXISTENCE. seL4 used this technique to validate their proofs actually caught real bugs.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 10 mutation operators defined (operand swap, guard drop, off-by-one, type change, etc)
- [ ] #2 Each mutation injected, .lean regenerated, build attempted
- [ ] #3 Mutations that should break proofs DO break proofs (true positives)
- [ ] #4 Any mutation that passes despite bug: documented as coverage gap
- [ ] #5 Coverage metric: X/10 mutations caught by proofs
<!-- AC:END -->
