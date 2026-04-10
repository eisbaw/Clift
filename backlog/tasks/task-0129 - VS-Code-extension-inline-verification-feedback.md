---
id: TASK-0129
title: 'VS Code extension: inline verification feedback'
status: To Do
assignee: []
created_date: '2026-04-10 15:30'
labels:
  - phase-j
  - tooling
  - industrial
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
For industrial adoption, verification must integrate with the developer workflow. Build a VS Code extension that: (1) shows verification status per-function (green/yellow/red), (2) highlights unproven obligations inline, (3) offers 'prove with Claude' action that invokes the proof engine, (4) displays proof chain from C to abstract spec. Study Lean 4's LSP integration and VS Code extension API.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 VS Code extension installed and connects to Lean LSP
- [ ] #2 Per-function verification status displayed in gutter
- [ ] #3 Unproven obligations highlighted with error squiggles
- [ ] #4 'Prove with AI' code action invokes Claude proof engine
- [ ] #5 Proof chain visualization (C -> CSimpl -> L1 -> ... -> spec)
<!-- AC:END -->
