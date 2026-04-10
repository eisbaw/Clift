---
id: TASK-0117
title: 'Mutual recursion: fixed-point L1corres proof construction'
status: To Do
assignee: []
created_date: '2026-04-10 15:29'
labels:
  - phase-f
  - lifting
  - critical-path
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Complete the mutual recursion gap. Currently 4/40 functions lack L1corres because they call other functions. Need: well-founded induction on call depth (or fuel-based with termination proof). The call graph is acyclic for ring_buffer_ext — this should be solvable with the existing topological sort by proving that all callees' L1corres are available before the caller's proof. If genuinely cyclic: use Lean 4's mutual/partial def + termination_by.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 All 40 ring_buffer_ext functions have L1corres proofs
- [ ] #2 Topological order ensures callee corres available before caller
- [ ] #3 Cyclic call graphs handled (at least: detected and reported)
- [ ] #4 No sorry
<!-- AC:END -->
