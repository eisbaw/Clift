---
id: TASK-0232
title: 'Custom Lean 4 linter: flag tautological FuncSpec postconditions'
status: To Do
assignee: []
created_date: '2026-04-11 23:03'
labels:
  - tooling
  - quality
  - linting
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Build a Lean 4 @[env_linter] that detects FuncSpec definitions where the postcondition is trivially true (provable by trivial/rfl/decide). This catches specs like 'count = count' that give a false sense of verification. The linter should also flag validHoare proofs that use validHoare_weaken_trivial_post. Add a 'just lint' recipe to the justfile that runs the linter across the codebase.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Lean 4 @[env_linter] implemented that finds all FuncSpec defs
- [ ] #2 Linter checks if post field is provable by trivial/rfl/decide and flags it
- [ ] #3 Linter also flags usage of validHoare_weaken_trivial_post
- [ ] #4 just lint recipe added to justfile that runs the linter
- [ ] #5 All current tautological specs flagged (rb_count_nodes, rb_sum, rb_count_above, rb_count_at_or_below)
<!-- AC:END -->
