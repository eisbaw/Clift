---
id: TASK-0060
title: 'CImporter: add lvar_nondet_init for uninitialized locals'
status: To Do
assignee: []
created_date: '2026-04-08 23:26'
labels:
  - cimporter
  - phase-2
  - soundness
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
AutoCorres2 uses lvar_nondet_init to model the nondeterministic initial value of uninitialized local variables. Our CImporter currently initializes locals via Inhabited default. This is unsound for verification: an uninitialized local should have a nondeterministic value, not a fixed default. For Phase 1 (gcd/max), all locals are assigned before use, so this is safe. But general C code needs this.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Uninitialized locals get nondeterministic initialization
- [ ] #2 Locals assigned before first use in gcd/max are unchanged
<!-- AC:END -->
