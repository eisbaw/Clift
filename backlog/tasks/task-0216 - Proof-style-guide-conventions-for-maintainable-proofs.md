---
id: TASK-0216
title: 'Proof style guide: conventions for maintainable proofs'
status: To Do
assignee: []
created_date: '2026-04-11 06:29'
labels:
  - maturity
  - documentation
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
As the proof base grows, consistency matters. Document: (1) when to use which tactic (simp vs rw vs exact vs omega), (2) naming conventions for lemmas, (3) the [local irreducible] pattern, (4) how to structure validHoare proofs, (5) when to split into helper lemmas, (6) how to write proofs that survive C code changes. seL4 had strict proof conventions — without them, maintenance becomes impossible.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Style guide in docs/proof-style-guide.md
- [ ] #2 Tactic usage conventions documented
- [ ] #3 Naming conventions for theorems/lemmas
- [ ] #4 validHoare proof template documented
- [ ] #5 Examples of good vs bad proof style from our codebase
<!-- AC:END -->
