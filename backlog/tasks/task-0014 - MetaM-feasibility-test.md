---
id: TASK-0014
title: MetaM feasibility test
status: To Do
assignee: []
created_date: '2026-04-08 21:35'
labels:
  - phase-0
  - test
  - risk-mitigation
dependencies:
  - TASK-0010
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Write a trivial Lean 4 metaprogram (in MetaM or TacticM) that programmatically constructs a CSimpl term and proves something about it. This validates that our types are MetaM-friendly before we invest in building the lifting stages. If MetaM cannot construct/manipulate our types, we need to redesign before Phase 1.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 MetaM program that constructs a CSimpl.skip term compiles
- [ ] #2 MetaM program that constructs a proof of Exec skip s (normal s) compiles
- [ ] #3 MetaM program can inspect CSimpl term structure (pattern match on constructors)
- [ ] #4 Feasibility assessment recorded: can MetaM build the proofs we need?
<!-- AC:END -->
