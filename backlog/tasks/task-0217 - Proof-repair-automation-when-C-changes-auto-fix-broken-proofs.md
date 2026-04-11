---
id: TASK-0217
title: 'Proof repair automation: when C changes, auto-fix broken proofs'
status: To Do
assignee: []
created_date: '2026-04-11 06:29'
labels:
  - maturity
  - ai
  - proof-engine
  - maintenance
dependencies:
  - TASK-0204
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
When a C file changes and proofs break, the proof engine should attempt auto-repair: (1) detect which proofs broke (lake build errors), (2) extract the new goal states, (3) feed to Claude with the OLD proof as context, (4) Claude adapts the proof to the new code. This is proof MAINTENANCE automation — the biggest long-term cost in formal verification. seL4 spent person-months on proof maintenance after kernel changes.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Broken proof detection from lake build output
- [ ] #2 Old proof + new goal fed to Claude as repair prompt
- [ ] #3 Tested: change ring buffer struct, auto-repair 3+ proofs
- [ ] #4 Success rate measured
<!-- AC:END -->
