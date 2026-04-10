---
id: TASK-0137
title: 'Full functional correctness: every operation does EXACTLY what spec says'
status: To Do
assignee: []
created_date: '2026-04-10 18:45'
labels:
  - phase-l
  - verification
  - depth
dependencies:
  - TASK-0136
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Our current proofs are 'invariant preservation' style — push preserves the queue invariant. seL4's proofs are FUNCTIONAL CORRECTNESS — push(q,x) in state s produces state s' where s'.queue = s.queue ++ [x] AND s'.count = s.count+1 AND s'.head unchanged AND every other memory location unchanged. Strengthen all 40 FuncSpecs to full functional correctness: postcondition specifies the EXACT resulting state, not just that an invariant holds.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 All 40 FuncSpecs strengthened to exact postconditions
- [ ] #2 push postcondition: queue = old_queue ++ [x], count = old_count + 1
- [ ] #3 pop postcondition: result = head(old_queue), queue = tail(old_queue)
- [ ] #4 peek postcondition: result = head(queue), state unchanged
- [ ] #5 Frame: every non-modified memory location provably unchanged
- [ ] #6 All validHoare proofs updated for strengthened specs
<!-- AC:END -->
