---
id: TASK-0216
title: 'Proof style guide: conventions for maintainable proofs'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-11 06:29'
updated_date: '2026-04-11 07:26'
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
- [x] #1 Style guide in docs/proof-style-guide.md
- [x] #2 Tactic usage conventions documented
- [x] #3 Naming conventions for theorems/lemmas
- [x] #4 validHoare proof template documented
- [x] #5 Examples of good vs bad proof style from our codebase
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Wrote comprehensive proof style guide in docs/proof-style-guide.md covering tactic conventions, naming, local irreducible, validHoare and L1corres templates, good vs bad examples from codebase.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Wrote docs/proof-style-guide.md: comprehensive proof conventions.

Covers:
- Tactic usage conventions (when to use simp vs rw vs omega etc.)
- Naming conventions for theorems/lemmas
- The [local irreducible] pattern with examples
- validHoare proof template
- L1corres proof template
- Good vs bad examples from our codebase
- When to split lemmas
- Proofs that survive C code changes
- maxHeartbeats/maxRecDepth guidance
<!-- SECTION:FINAL_SUMMARY:END -->
