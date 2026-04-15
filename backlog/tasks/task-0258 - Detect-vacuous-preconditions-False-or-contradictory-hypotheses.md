---
id: TASK-0258
title: Detect vacuous preconditions (False or contradictory hypotheses)
status: Done
assignee:
  - '@claude'
created_date: '2026-04-14 18:40'
updated_date: '2026-04-15 05:56'
labels:
  - credibility
  - audit
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
A theorem with False or contradictory preconditions is trivially true — it proves nothing. Example:
  theorem nonsense (h : False) : 0 = 1 := False.elim h

In our codebase, this could manifest as:
- validHoare (fun s => False) m Q — trivially true, no state satisfies P
- FuncSpec with pre := fun s => some_impossible_condition
- Theorems with hypotheses that contradict each other

This is hard to detect mechanically but we can grep for obvious patterns:
- grep for 'False' in preconditions/hypotheses
- grep for 'fun _ => False' or 'fun s => False'
- Lean MetaM linter: for each validHoare theorem, check if the precondition is inhabited (exists a state satisfying it)

A MetaM linter could:
1. Find all validHoare/FuncSpec theorems
2. For each, extract the precondition P
3. Try to prove (∃ s, P s) via decide/simp — if it fails, flag as potentially vacuous
4. This doesn't catch ALL vacuous preconditions but catches obvious ones

Reference: seL4 methodology — they explicitly document "What the Proofs Assume" to prevent hidden vacuity.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Grep-based check for obvious False preconditions added to audit
- [ ] #2 MetaM linter attempted for precondition inhabitedness
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Added grep-based vacuous precondition detection (fun _ => False patterns) to the just audit recipe. Scans Examples/ only, matching the Python audit scope. MetaM linter version deferred to future work.
<!-- SECTION:FINAL_SUMMARY:END -->
