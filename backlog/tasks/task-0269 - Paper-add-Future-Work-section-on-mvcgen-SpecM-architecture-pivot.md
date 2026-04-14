---
id: TASK-0269
title: 'Paper: add Future Work section on mvcgen/SpecM architecture pivot'
status: To Do
assignee: []
created_date: '2026-04-14 21:35'
labels:
  - paper
dependencies: []
documentation:
  - >-
    backlog/docs/doc-0001 -
    Sebastian-Ullrich-feedback-Std.Do.Triple-mvcgen-skip-CSimpl.md
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Sebastian Graf (Lean FRO) suggested replacing custom validHoare with Std.Do.Triple + mvcgen, and skipping CSimpl by emitting monadic SpecM code directly from CImporter. His LeanCorres PoC (github.com/sgraf812/LeanCorres) validates the approach. This should be captured as Future Work in the paper, not as current architecture.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Future Work section describes the mvcgen/SpecM pivot
- [ ] #2 References LeanCorres PoC and Sebastian Graf feedback
- [ ] #3 Explains tradeoffs: complexity reduction vs TCB expansion
- [ ] #4 Notes that while loops and nondeterminism are supported by SpecM (not a blocker)
<!-- AC:END -->
