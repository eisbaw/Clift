---
id: TASK-0055
title: Design exception channel for NondetM (throw/catch support)
status: Done
assignee:
  - '@claude'
created_date: '2026-04-08 22:39'
updated_date: '2026-04-09 19:43'
labels:
  - design
  - monadlib
  - phase-1
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
seL4's L1 monad (exn_monad) has built-in exception support (Exn/Result). Our NondetM only has results+failure with no exception channel. SimplConv (L1) needs to translate CSimpl throw/catch into monadic operations. Either: (a) extend NondetM with an exception return channel, or (b) use a wrapper type like ExceptT over NondetM, or (c) encode exceptions via the Outcome type in results. This is a design decision that affects the entire pipeline.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Design decision documented as ADR
- [x] #2 Exception-aware monadic operations (throw, catch) available
- [x] #3 SimplConv can translate CSimpl throw/catch
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Already resolved by ADR-001 (backlog/docs/adr-001-l1-exception-encoding.md).

The design decision was: L1Monad σ := NondetM σ (Except Unit Unit). Normal -> Except.ok (), Abrupt -> Except.error (), Fault -> NondetM failure flag. NondetM itself was intentionally NOT modified (per plan.md).

L1 combinators in SimplConv.lean provide: L1.throw, L1.catch, L1.seq (with exception propagation). L1corres_throw and L1corres_catch are fully proved theorems. No NondetM-level exception channel was needed because the L1 return type encoding handles it.
<!-- SECTION:FINAL_SUMMARY:END -->
