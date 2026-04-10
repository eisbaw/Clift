---
id: TASK-0139
title: Prove absence of all undefined behavior in ring_buffer_ext
status: To Do
assignee: []
created_date: '2026-04-10 18:45'
labels:
  - phase-l
  - verification
  - ub-freedom
dependencies:
  - TASK-0137
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
seL4 proves the C code has NO undefined behavior — no null derefs, no buffer overflows, no signed overflow, no use-after-free, no double-free. Our totalHoare (total correctness) implies no UB because UB = fault = failure, and totalHoare proves no failure. Prove totalHoare (not just validHoare) for all 40 functions. This means: every guard in the CSimpl is proven to hold, not just assumed.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 totalHoare proven for all 40 functions (not just validHoare)
- [ ] #2 Every CSimpl.guard obligation discharged
- [ ] #3 Null dereference: proven impossible for all pointer accesses
- [ ] #4 Buffer overflow: proven impossible for all array accesses
- [ ] #5 Division by zero: proven impossible for all divisions
- [ ] #6 No sorry
<!-- AC:END -->
