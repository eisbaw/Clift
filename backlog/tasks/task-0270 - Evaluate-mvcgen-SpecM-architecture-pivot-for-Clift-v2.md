---
id: TASK-0270
title: Evaluate mvcgen/SpecM architecture pivot for Clift v2
status: To Do
assignee: []
created_date: '2026-04-14 21:35'
updated_date: '2026-04-14 21:37'
labels:
  - architecture
  - future
  - needs-decision
dependencies: []
documentation:
  - >-
    backlog/docs/doc-0001 -
    Sebastian-Ullrich-feedback-Std.Do.Triple-mvcgen-skip-CSimpl.md
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Sebastian Graf (Lean FRO) suggested two major changes: (1) Replace custom validHoare + L1HoareRules with Std.Do.Triple + mvcgen, (2) Skip CSimpl deep embedding, emit monadic SpecM code directly from CImporter. His LeanCorres PoC (github.com/sgraf812/LeanCorres) demonstrates feasibility. This task is to evaluate and prototype the pivot.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Prototype SpecM monad (port from LeanCorres or define from scratch) with WP/WPMonad instances
- [ ] #2 Verify mvcgen works on one Clift example (e.g. gcd while loop)
- [ ] #3 Evaluate TCB impact of absorbing CSimpl->L1 translation into CImporter
- [ ] #4 Determine if CImporter can emit do-notation SpecM code that mvcgen processes
- [ ] #5 Assess whether LeanCorres whileLoop + WhileInvariant pattern covers all Clift loop cases
- [ ] #6 Document decision: adopt, adapt, or defer
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Blocked pending human decision on whether to pursue this pivot. Depends on paper timeline, sorry elimination progress, and whether to collaborate with Sebastian Graf on shared SpecM foundation.
<!-- SECTION:NOTES:END -->
