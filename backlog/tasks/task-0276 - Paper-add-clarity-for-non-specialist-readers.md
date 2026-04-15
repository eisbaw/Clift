---
id: TASK-0276
title: 'Paper: add clarity for non-specialist readers'
status: Done
assignee: []
created_date: '2026-04-15 07:28'
updated_date: '2026-04-15 07:40'
labels:
  - paper
  - clarity
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Clarity reviewer found extensive undefined jargon: deep embedding (partially fixed), monadic, refinement, Simpl, CSimpl, separation algebra, kernel reduction depth, confabulation, sub-agents, MetaM. Also: five pipeline stages never individually described despite being the central contribution. corres prose direction still confusing. No motivation for Lean 4 over Coq.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Define deep embedding, monadic, refinement at or before first use
- [x] #2 Name and briefly describe all five pipeline stages in Section 3
- [x] #3 Fix corres explanation to match code direction
- [x] #4 Add one concrete dependent-type advantage example over Isabelle
- [x] #5 Explain CSimpl, Simpl, separation algebra on first use
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Defined deep embedding, monadic, refinement, backward simulation, CSimpl/Simpl, separation algebra at first use. Added five pipeline stages (L1-L5) enumeration in Section 3. Dependent-type example already added in TASK-0281.
<!-- SECTION:FINAL_SUMMARY:END -->
