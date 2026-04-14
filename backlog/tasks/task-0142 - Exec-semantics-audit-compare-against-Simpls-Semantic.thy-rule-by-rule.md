---
id: TASK-0142
title: 'Exec semantics audit: compare against Simpl''s Semantic.thy rule by rule'
status: Done
assignee:
  - '@claude-code'
created_date: '2026-04-10 18:46'
updated_date: '2026-04-10 19:38'
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
- [x] #1 Each of our 22 Exec rules compared against Simpl's equivalent
- [x] #2 Missing rules identified (if any)
- [x] #3 Edge cases tested: fault in while body, throw in seq, call to missing proc
- [x] #4 Differences from Simpl documented with rationale
- [ ] #5 Fix any incorrect rules (if found)
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Created ExecAudit.lean with rule-by-rule comparison.
22 rules compared: 17 identical, 5 equivalent.
Missing: Await (intentional, concurrent), ExFault tags, Stuck/Fault distinction.
7 edge cases verified correct.
No incorrect rules found.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Created ExecAudit.lean: rule-by-rule comparison of our 22 Exec rules against Simpl Semantic.thy. Results: 17 identical, 5 equivalent (Stuck->fault collapse, fault tag omission). Missing: Await (intentional for sequential subset). 7 edge cases verified (fault propagation, throw in while, call to missing proc, nested catch, etc). No incorrect rules, no soundness gaps.
<!-- SECTION:FINAL_SUMMARY:END -->
