---
id: TASK-0084
title: 'Unified ''clift'' command: one-shot full pipeline'
status: To Do
assignee: []
created_date: '2026-04-10 05:17'
labels:
  - phase-a
  - metam
  - automation
  - milestone
dependencies:
  - TASK-0083
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Create a single Lean 4 command 'clift' that runs the entire pipeline on a Generated file: L1 (SimplConv) -> L2 (LocalVarExtract) -> L3 (TypeStrengthen) -> L5 (WordAbstract). After running 'clift', each function has a clean user-facing type with a composed corres chain back to C. This is the equivalent of AutoCorres2's 'autocorres' command.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 'clift' command defined as Lean 4 command elaborator
- [ ] #2 Processes all functions in a Generated module
- [ ] #3 Produces: one definition + one corres theorem per function
- [ ] #4 Composed corres: corres_trans chains L1->L2->L3->L5
- [ ] #5 Tested on Generated/Gcd.lean, Generated/Swap.lean, all Generated files
- [ ] #6 No sorry
- [ ] #7 Performance: <30s for a 10-function file
<!-- AC:END -->
