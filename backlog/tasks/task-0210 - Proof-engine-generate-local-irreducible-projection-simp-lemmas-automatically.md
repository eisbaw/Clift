---
id: TASK-0210
title: >-
  Proof engine: generate [local irreducible] + projection simp lemmas
  automatically
status: To Do
assignee: []
created_date: '2026-04-11 06:29'
labels:
  - proof-engine
  - automation
  - critical-path
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The SwapProof pattern requires per-function projection lemmas (swap_f1_globals, etc). Currently these are written manually. The proof engine should generate them automatically: for each L1.modify step function, inspect the lambda body, generate @[simp] projection lemmas for each struct field. This is the key automation that makes the pattern scalable.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Given an L1.modify lambda, auto-generate projection simp lemmas
- [ ] #2 Lemmas are rfl proofs with [local irreducible] hVal heapUpdate
- [ ] #3 Generated lemmas compile
- [ ] #4 Integrated into proof engine prompt construction
- [ ] #5 Tested on swap (3 steps) and ring buffer push (~8 steps)
<!-- AC:END -->
