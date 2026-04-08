---
id: TASK-0014
title: MetaM feasibility test
status: Done
assignee:
  - '@mped'
created_date: '2026-04-08 21:35'
updated_date: '2026-04-08 23:04'
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
- [x] #1 MetaM program that constructs a CSimpl.skip term compiles
- [x] #2 MetaM program that constructs a proof of Exec skip s (normal s) compiles
- [x] #3 MetaM program can inspect CSimpl term structure (pattern match on constructors)
- [x] #4 Feasibility assessment recorded: can MetaM build the proofs we need?
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
- All 4 test categories pass
- CSimpl terms: skip, basic, seq, cond, catch, throw all constructible
- Exec proof terms: Exec.skip proof constructed and type-checked
- Pattern matching: getAppFn approach identifies all 11 constructors
- Complex structures: max_body-like catch/cond/seq/basic/throw builds correctly
- Lambda construction via Expr.lam is straightforward
- Assessment: GO for lifting pipeline MetaM implementation
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
MetaM feasibility test passes.

All CSimpl constructors constructible in MetaM via simple mkApp/mkAppN.
Exec proof terms constructible as direct constructor applications.
CSimpl term inspection works via getAppFn pattern matching.
Complex term structures (catch/cond/seq/basic/throw) build and type-check.

Assessment: GO. MetaM is fully capable of building the terms and proofs
needed for the lifting pipeline.
<!-- SECTION:FINAL_SUMMARY:END -->
