---
id: TASK-0205
title: 'Batch sorry elimination: run proof engine on all 57 sorry'
status: To Do
assignee:
  - '@claude'
created_date: '2026-04-11 06:28'
updated_date: '2026-04-11 08:44'
labels:
  - critical-path
  - ai
  - sorry-elimination
dependencies:
  - TASK-0204
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Run clift-prove-by-claudecode --batch on every file with sorry. For each: extract goal, build prompt with [local irreducible] hint + projection lemma pattern + similar proofs from ProofIndex, call Claude, apply result, check with lake build. Track: first-attempt success, retry success, failure. Target: eliminate 45/57 sorry (80%). Remaining ~12 are the genuinely hard ones needing human insight or MetaM VCG.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Proof engine run on all 57 sorry
- [ ] #2 First-attempt success rate measured
- [ ] #3 Retry (3x) success rate measured
- [ ] #4 At least 45/57 sorry eliminated
- [ ] #5 Remaining sorry categorized: why Claude failed, what's needed
- [ ] #6 Total API cost measured
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Framework complete, awaiting API key. The clift-prove-by-claudecode script exists and implements the batch sorry elimination pipeline: extract goal, build prompt with [local irreducible] hint + projection lemma pattern + similar proofs from ProofIndex, call Claude API, apply result, check with lake build. Cannot execute without Claude API key configured. Current sorry count is 31 in RBExtFuncSpecs + 3 in RBExtRefinement + others scattered across proof files.
<!-- SECTION:FINAL_SUMMARY:END -->
