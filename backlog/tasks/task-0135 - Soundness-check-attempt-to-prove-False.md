---
id: TASK-0135
title: 'Soundness check: attempt to prove False'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-10 18:45'
updated_date: '2026-04-10 19:13'
labels:
  - phase-l
  - soundness
  - critical
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The cheapest, highest-value test. If we can prove False without sorry, the entire system is unsound and every proof is meaningless. Try: (1) derive False from corres + L1corres assumptions, (2) derive False from the memory model (heapPtrValid + hVal + heapUpdate), (3) derive False from the Exec semantics, (4) derive False from NondetM + Hoare triples. If any succeed: we have a critical bug. If all fail: confidence boost. seL4 had multiple independent kernel checkers specifically to catch this class of error.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Attempted: prove False from corres definitions alone
- [x] #2 Attempted: prove False from memory model
- [x] #3 Attempted: prove False from Exec semantics
- [x] #4 Attempted: prove False from NondetM/Hoare
- [x] #5 Attempted: prove False from L1corres bridge
- [x] #6 Result documented: all attempts failed (good) or bug found (critical)
- [x] #7 If bug found: filed as blocking task with fix
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Soundness check complete. Attempted to prove False from 6 areas: corres definitions, memory model, Exec semantics, NondetM/Hoare, L1corres bridge, and Terminates/cHoareTotal. All attempts failed (the expected outcome), meaning no obvious logical inconsistencies in the system. Each failed attempt is documented with detailed reasoning in Examples/SoundnessCheck.lean. Two positive sanity theorems proven: select_empty_validHoare (partial correctness with empty results is vacuously true) and select_empty_not_totalHoare (total correctness correctly rejects empty results). No sorry in the file.
<!-- SECTION:FINAL_SUMMARY:END -->
