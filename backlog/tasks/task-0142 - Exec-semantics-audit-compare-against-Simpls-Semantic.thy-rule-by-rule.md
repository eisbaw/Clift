---
id: TASK-0142
title: 'Exec semantics audit: compare against Simpl''s Semantic.thy rule by rule'
status: To Do
assignee: []
created_date: '2026-04-10 18:46'
labels:
  - phase-m
  - testing
  - soundness
dependencies: []
references:
  - ext/AutoCorres2/c-parser/Simpl/Semantic.thy
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Our Exec has 22 rules. Simpl's Semantic.thy has more. Audit each of our Exec rules against Simpl's to check: (1) are we missing any rules? (2) are any rules wrong? (3) do our rules handle all edge cases (e.g., while loop body throws, seq first command faults)? Specifically check: fault propagation, abrupt propagation through seq/catch/while, call with missing proc, guard with undecidable predicate.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Each of our 22 Exec rules compared against Simpl's equivalent
- [ ] #2 Missing rules identified (if any)
- [ ] #3 Edge cases tested: fault in while body, throw in seq, call to missing proc
- [ ] #4 Differences from Simpl documented with rationale
- [ ] #5 Fix any incorrect rules (if found)
<!-- AC:END -->
