---
id: TASK-0055
title: Design exception channel for NondetM (throw/catch support)
status: To Do
assignee: []
created_date: '2026-04-08 22:39'
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
- [ ] #1 Design decision documented as ADR
- [ ] #2 Exception-aware monadic operations (throw, catch) available
- [ ] #3 SimplConv can translate CSimpl throw/catch
<!-- AC:END -->
