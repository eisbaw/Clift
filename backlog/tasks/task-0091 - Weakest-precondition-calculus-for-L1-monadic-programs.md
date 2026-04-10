---
id: TASK-0091
title: Weakest precondition calculus for L1 monadic programs
status: To Do
assignee: []
created_date: '2026-04-10 05:18'
labels:
  - phase-c
  - automation
  - wp
dependencies:
  - TASK-0087
references:
  - ext/AutoCorres2/lib/Monad_WP/NonDetMonadVCG.thy
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Implement wp (weakest precondition) calculation for L1 monadic programs. Given a postcondition Q and a program c, compute the weakest P such that {P} c {Q}. This is the standard VCG technique — seL4 uses it extensively. The wp for seq is: wp(c1;c2, Q) = wp(c1, wp(c2, Q)). The wp for guard is: wp(guard p; c, Q) = p /\ wp(c, Q). Study ext/AutoCorres2/lib/Monad_WP/NonDetMonadVCG.thy.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 wp function defined for L1 combinators: skip, modify, guard, seq, catch, throw
- [ ] #2 wp_sound theorem: {wp c Q} c {Q} proven
- [ ] #3 wp_complete theorem: if {P} c {Q} then P -> wp c Q
- [ ] #4 wp for while: requires user-supplied invariant I, generates I /\ cond -> wp(body, I)
- [ ] #5 wp for call: uses function spec (not body)
- [ ] #6 Tested: wp-based proof of swap is shorter than manual proof
<!-- AC:END -->
