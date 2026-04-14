---
id: TASK-0217
title: 'Proof repair automation: when C changes, auto-fix broken proofs'
status: To Do
assignee:
  - '@claude'
created_date: '2026-04-11 06:29'
updated_date: '2026-04-14 22:11'
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

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Design document written: docs/proof-repair-automation.md. Covers the full repair pipeline: error parser extracts broken theorems from lake build output, old proof retrieval via git, goal diffing (structural comparison), repair prompt construction with old proof + new goal + diff analysis, validation loop with retry. Identifies 5 change categories (field rename, field addition, logic change, new function, function removal) with confidence levels. Estimated implementation effort: 7 days. No code implementation -- this is a design task.
<!-- SECTION:FINAL_SUMMARY:END -->
