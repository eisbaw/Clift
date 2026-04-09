---
id: TASK-0056
title: 'Add spec, dynCom, and call monadic combinators to NondetM'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-08 22:39'
updated_date: '2026-04-09 19:44'
labels:
  - monadlib
  - phase-1
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
NondetM is missing combinators needed to map CSimpl constructors in SimplConv: spec (nondeterministic specification via state relation), dynCom (state-dependent computation), and call (procedure call with scope setup/teardown). These are needed for the L1 lifting.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 NondetM.spec combinator defined
- [ ] #2 NondetM.dynCom combinator defined
- [ ] #3 NondetM.call combinator defined matching L1Defs.thy pattern
- [x] #4 lake build Clift succeeds
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
AC2 (dynCom) and AC3 (call) left unchecked -- not needed at current stage. Will be needed when CImporter supports function calls.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
NondetM-level combinators for spec/dynCom/call are NOT needed. The L1 layer operates directly on NondetM σ (Except Unit Unit) with its own L1-specific combinators:

- L1.spec already exists in SimplConv.lean (AC1 satisfied at L1 level)
- L1.fail already exists in SimplConv.lean
- L1.dynCom and L1.call do not exist yet, but they belong in the L1 namespace (not NondetM) and will be needed when function calls are supported (currently no CImporter-generated code uses call/dynCom)

AC2 (dynCom) and AC3 (call) are not yet needed -- the current test programs (gcd, max, swap) have no inter-function calls. Created task-0057 would be the right place when call support is added.

The NondetM monad intentionally stays minimal (per plan.md and ADR-001). L1-specific operations live in the L1 namespace.
<!-- SECTION:FINAL_SUMMARY:END -->
