---
id: TASK-0257
title: 'Add @[csimp] axiom smuggling detection to audit'
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
Lean GitHub #7463: @[csimp] simp lemmas using axioms don't propagate axiom dependencies through native_decide. This means a proof can depend on a custom axiom (even sorry) without #print axioms revealing it.

We currently have 0 @[csimp] uses, but this should be detected if anyone adds one.

Add to just audit:
  grep -rn "@\[csimp\]" --include="*.lean" Clift/ Examples/
Any hit in proof-critical code is a red flag — the simp lemma's axiom dependencies won't be tracked.

Also add @[implemented_by] detection (0 uses currently, but equally dangerous — bypasses kernel entirely).

Reference: https://github.com/leanprover/lean4/issues/7463
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 @[csimp] detection added to just audit
- [x] #2 @[implemented_by] detection added to just audit
- [x] #3 Both pass clean (0 uses)
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Added @[csimp] and @[implemented_by] detection to the just audit recipe as bash sanity checks. Both grep Clift/ and Examples/ .lean files. Both pass clean with 0 hits.
<!-- SECTION:FINAL_SUMMARY:END -->
