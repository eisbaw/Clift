---
id: TASK-0144
title: 'Independent Lean kernel check: export and re-check proofs'
status: To Do
assignee: []
created_date: '2026-04-10 18:46'
labels:
  - phase-m
  - soundness
  - hardening
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
seL4 has multiple independent kernel checkers. Lean 4 exports .olean files checked by the kernel, but we should verify: (1) run 'lean --check' on all .olean files, (2) use #print axioms on every theorem to verify no unexpected axioms, (3) export key theorems to a standalone file that imports nothing and re-checks. This is defense-in-depth: even if lake build says success, verify the kernel actually checked everything.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 #print axioms run on: corres_trans, L1corres_seq, L1corres_while, swap_correct, gcd_correct_nat
- [ ] #2 Each theorem depends only on propext, Quot.sound, Classical.choice (standard)
- [ ] #3 No theorem depends on sorryAx
- [ ] #4 Standalone check file created and verified
- [ ] #5 Documented: our trusted base is exactly Lean 4 kernel + CImporter
<!-- AC:END -->
