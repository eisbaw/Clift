---
id: TASK-0082
title: 'MetaM L3 TypeStrengthen: auto-narrow monad type'
status: To Do
assignee: []
created_date: '2026-04-10 05:17'
labels:
  - phase-a
  - metam
  - automation
dependencies:
  - TASK-0081
references:
  - ext/AutoCorres2/type_strengthen.ML
  - ext/AutoCorres2/TypeStrengthen.thy
  - ext/AutoCorres2/monad_types.ML
  - Clift/Lifting/TypeStrengthen.lean
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Port AutoCorres2's type_strengthen.ML to Lean 4 MetaM. Given an L2 function in the full NondetM monad, analyze whether it can be strengthened to pure (no state, no failure) or option (may fail). Pattern-match the L2 term structure against ts_rules. Generate L3corres proof. Currently manual (Examples/GcdTypeStrengthen.lean).
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 MetaM command 'clift_l3' narrows monad for each function
- [ ] #2 Pure functions detected and typed as α (not NondetM)
- [ ] #3 Failing functions typed as Option
- [ ] #4 L3corres proof generated automatically
- [ ] #5 gcd correctly identified as pure
- [ ] #6 No sorry
<!-- AC:END -->
