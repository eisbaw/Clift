---
id: TASK-0170
title: 'Termination predicate: total correctness proofs for bounded operations'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-10 18:53'
updated_date: '2026-04-10 19:14'
labels:
  - phase-l
  - soundness
  - seL4-parity
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
seL4 proved all kernel operations terminate (bounded execution). Clift's Exec semantics only give partial correctness (non-termination = no derivation). Need: (1) Define 'terminates' inductive predicate following Simpl's Terminates.thy, (2) Define totalHoare as validHoare + termination, (3) Prove termination for all ring_buffer_ext functions (they are all bounded), (4) Establish the pattern: partial correctness + termination = total correctness. Without this, we cannot prove liveness or progress -- a function could satisfy its Hoare triple by simply never returning. seL4 parity REQUIRES total correctness for all verified functions.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Terminates inductive predicate defined following Simpl
- [x] #2 totalHoare combines partial correctness + terminates
- [x] #3 At least 5 ring_buffer_ext functions proven to terminate
- [x] #4 Pattern documented: how to prove total correctness
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Terminates predicate was already in Exec.lean. Added TerminatesProps.lean with:
- Terminates_implies_Exec (key theorem, no sorry)
- cHoareTotal_iff, cHoareTotal_implies_exists_outcome
- Convenience lemmas for building termination proofs

7 ring_buffer_ext functions proven to terminate.
Total correctness pattern demonstrated.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Implemented Terminates predicate properties and termination proofs:

1. TerminatesProps.lean: Key theorem Terminates_implies_Exec (if a program terminates, there exists an Exec outcome). Proven by structural induction on Terminates, no sorry. Also: cHoareTotal_iff, cHoareTotal_implies_exists_outcome, convenience lemmas.

2. TerminationProofs.lean: 7 ring_buffer_ext functions proven to terminate (rb_capacity, rb_size, rb_remaining, rb_is_empty, rb_is_full, rb_stats_total_ops, rb_iter_has_next). All loop-free, so termination follows from structural decomposition. Reusable helper lemmas for common CSimpl patterns.

3. Total correctness pattern documented and demonstrated: cHoareTotal = cHoare + Terminates.
<!-- SECTION:FINAL_SUMMARY:END -->
