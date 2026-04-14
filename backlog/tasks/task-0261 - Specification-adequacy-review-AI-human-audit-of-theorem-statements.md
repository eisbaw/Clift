---
id: TASK-0261
title: 'Specification adequacy review: AI + human audit of theorem statements'
status: To Do
assignee: []
created_date: '2026-04-14 18:40'
labels:
  - credibility
  - specification
  - review
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The hardest credibility question: does the theorem statement actually capture what we want to prove?

No tool can fully answer this — it requires understanding the INTENT of the verification. But we can build tooling to assist:

1. AI REVIEW SKILL/PERSONA:
Create a Claude Code sub-agent persona 'spec-reviewer' that:
- Reads each FuncSpec definition and the corresponding C source code
- Asks: does the postcondition actually constrain the function's behavior?
- Checks: could a trivially wrong implementation satisfy the spec?
- Checks: are there important behaviors NOT captured by the spec?
- Flags: tautological postconditions, overly weak preconditions, missing invariants
- Reports: for each spec, a confidence score (strong/adequate/weak/tautological)

The persona should know about common specification gaps:
- Read-only functions: spec should say state unchanged (not just count=count)
- Mutation functions: spec should say WHAT changed and HOW
- Loop functions: spec should relate output to input (e.g., sum = Σ values)
- Inter-procedural: spec should compose correctly with callee specs

2. HUMAN REVIEW CHECKLIST:
For each FuncSpec, a human reviewer should verify:
- [ ] Postcondition is NON-TRIVIAL (not provable without knowing what the function does)
- [ ] Postcondition CONSTRAINS behavior (would fail for a wrong implementation)
- [ ] Precondition is SATISFIABLE (there exist states meeting it)
- [ ] Precondition is NECESSARY (weakening it would make the proof impossible)
- [ ] The spec matches the C programmer's INTENT (not just what's provable)

3. MUTATION TESTING FOR SPECS:
Automatically mutate the C code (change + to -, swap arguments, etc.) and check if the spec still holds. If a mutation doesn't break the spec, the spec is too weak.

Reference: seL4 layers — Abstract Spec (human-readable intent) → Executable Spec → Implementation
Reference: CLEVER benchmark — specification leakage problem
Reference: "What the Proofs Imply" — seL4's explicit documentation of proof scope
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 spec-reviewer persona/skill created
- [ ] #2 All 40 ring buffer FuncSpecs reviewed and rated
- [ ] #3 All tautological specs identified and strengthened (TASK-0231)
- [ ] #4 Mutation testing prototype for at least 5 functions
- [ ] #5 Human review checklist documented and applied to key proofs
<!-- AC:END -->
