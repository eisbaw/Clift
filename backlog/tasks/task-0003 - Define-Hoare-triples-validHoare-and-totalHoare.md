---
id: TASK-0003
title: 'Define Hoare triples: validHoare and totalHoare'
status: Done
assignee:
  - '@mped'
created_date: '2026-04-08 21:33'
updated_date: '2026-04-08 22:34'
labels:
  - phase-0
  - monadlib
dependencies:
  - TASK-0001
references:
  - Clift/MonadLib/Hoare.lean
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Define partial correctness (validHoare) and total correctness (totalHoare) Hoare triples over NondetM. totalHoare = validHoare + termination (results nonempty). Follow plan.md Decision 6.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 validHoare definition compiles and matches plan.md spec
- [x] #2 totalHoare definition compiles: validHoare + Nonempty results
- [x] #3 Basic sanity lemma: validHoare True (pure x) (fun r _ => r = x) proven
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
validHoare and totalHoare defined matching plan.md spec exactly. Sanity lemma validHoare_pure and totalHoare_pure both proven with no sorry.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Defined validHoare and totalHoare in Clift/MonadLib/Hoare.lean matching plan.md Decision 6. validHoare P m Q requires no-failure and all results satisfy Q. totalHoare adds nonemptiness of results. Proved sanity lemmas validHoare_pure and totalHoare_pure.
<!-- SECTION:FINAL_SUMMARY:END -->
